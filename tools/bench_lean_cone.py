#!/usr/bin/env python3
"""Turn the three-certificate anecdote in `Forge.Checker.Corpus` into a
measurement.

WHAT THIS DOES. It generates a family of polynomial nonnegativity problems whose
certificates are known *by construction* rather than found by search: pick
random integer (or rational) polynomials `q_i`, nonnegative weights `w_i`,
optionally some guard polynomials `g_k` and one equality constraint `f`, and set

    p  =  sum_i w_i * (prod_k g_k^e_ik) * q_i^2  +  h * f

Then `p >= 0` wherever every `g_k >= 0` and `f = 0`, and the certificate is the
data that built it. No search, no SDP, no trust in a solver. It also generates
NEGATIVE CONTROLS -- certificates that are wrong in one specific way -- because
a benchmark on which everything passes measures nothing.

Both sides are then emitted as Lean and run:

  * `lean/Forge/Checker/Bench.lean` -- the checker route. Every problem gets the
    same four-theorem treatment `Corpus.lean` gets, produced by the SAME emitter
    (`tools/export_lean_cone.emit`), so the comparison is against the real
    artifact and not a simplified stand-in.
  * one throwaway file per problem per tactic, in a scratch directory -- the
    automation route: the identical goal, in ordinary arithmetic, handed to
    core Lean's `grind` and `omega` with no certificate at all.

The only edit made to the shared emitter's output is one sentence: `emit` says
"The prototype's certificate is over the rationals", which is true of
`Corpus.lean` and false here, where the certificates were constructed by this
script. Replacing that sentence is cheaper and more honest than forking the
emitter.

REUSE. Everything about the conversion and the Lean syntax -- `convert`,
`emit`, `lean_poly`, `lean_concrete`, `lean_env`, and the rational polynomial
arithmetic -- comes from `tools/export_lean_cone.py` unchanged. This script adds
problem generation, the negative controls, the timing harness, and nothing else.
"""
from __future__ import annotations

import argparse
import copy
import json
import os
import random
import subprocess
import sys
import time
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

from export_lean_cone import (  # noqa: E402
    convert,
    emit,
    lean_concrete,
    lean_ident,
    lean_int,
    lean_poly,
    normalise,
    parse_poly,
    poly_add,
    poly_eq,
    poly_mul,
    poly_pow,
)

LEAN_DIR = ROOT / "lean"
LIB = LEAN_DIR / ".lake" / "build" / "lib"

# The one sentence in the shared emitter's prose that is true of Corpus.lean and
# not of this file. See the module docstring.
PROTOTYPE_SENTENCE = "The prototype's certificate is over the rationals."
BENCH_SENTENCE = "This certificate was built by construction, not found by search."


# ---------------------------------------------------------------------------
# Problem generation.
# ---------------------------------------------------------------------------
def monos(nvars: int, deg: int, exact: bool = False) -> list:
    """Every exponent vector of total degree <= `deg` (or == `deg`)."""
    out: list = []

    def rec(prefix: list, used: int, k: int) -> None:
        if k == nvars:
            if not exact or used == deg:
                out.append(tuple(prefix))
            return
        for e in range(deg - used + 1):
            rec(prefix + [e], used + e, k + 1)

    rec([], 0, 0)
    return out


def rand_bundle(rng, nvars, deg, cmax, nterms, denominators=False) -> dict:
    """A random polynomial in the prototype's bundle shape.

    One term of total degree exactly `deg` is always present, so the degree is
    what it is claimed to be. Coefficients are drawn from the upper part of
    `[1, cmax]`, so a "large coefficient" family really is large throughout and
    not large in one monomial only.
    """
    pool = monos(nvars, deg)
    top = monos(nvars, deg, exact=True)
    head = rng.choice(top)
    rest = [m for m in pool if m != head]
    rng.shuffle(rest)
    chosen = [head] + rest[: max(0, nterms - 1)]
    terms = []
    for m in chosen:
        c = rng.randint(max(1, cmax // 3), cmax) * rng.choice([1, -1])
        if denominators and rng.random() < 0.5:
            terms.append([list(m), "%d/%d" % (c, rng.choice([2, 3, 4]))])
        else:
            terms.append([list(m), c])
    return {"n": nvars, "terms": terms}


def to_bundle(nvars: int, rp) -> dict:
    """Collect a rational polynomial back into bundle shape."""
    d = normalise(rp)
    terms = []
    for m in sorted(d):
        c = d[m]
        terms.append([list(m), int(c) if c.denominator == 1 else str(c)])
    return {"n": nvars, "terms": terms}


def assemble(sq_specs, ineqs, eqs, mults):
    """`sum_i w_i (prod g^e) q_i^2 + sum_j h_j f_j`, over the rationals."""
    p: list = []
    for spec in sq_specs:
        term = [((), Q(spec["weight"]))]
        for k, e in enumerate(spec["powers"]):
            term = poly_mul(term, poly_pow(parse_poly(ineqs[k]), e))
        q = parse_poly(spec["square"])
        term = poly_mul(term, poly_mul(q, q))
        p = poly_add(p, term)
    for h, f in zip(mults, eqs):
        p = poly_add(p, poly_mul(parse_poly(h), parse_poly(f)))
    return p


def var_poly(nvars: int, i: int) -> dict:
    return {"n": nvars, "terms": [[[1 if j == i else 0 for j in range(nvars)], 1]]}


def build_record(rng, spec: dict) -> dict:
    """One problem, in the shape `export_lean_cone.convert` consumes."""
    nvars = spec["nvars"]
    qdeg = spec["qdeg"]
    nsq = spec["squares"]
    cmax = spec["cmax"]
    nineq = spec.get("ineqs", 0)
    neq = spec.get("eqs", 0)
    rational = spec.get("rational", False)

    ineqs = [var_poly(nvars, k % nvars) for k in range(nineq)]

    eqs, mults = [], []
    for _ in range(neq):
        # A linear equality constraint, and a multiplier of whatever degree
        # keeps the target inside the family's degree.
        eqs.append(rand_bundle(rng, nvars, 1, max(2, cmax // 8), nvars + 1))
        mults.append(rand_bundle(rng, nvars, max(1, 2 * qdeg - 1),
                                 max(2, cmax // 8), 3))

    sq_specs = []
    for i in range(nsq):
        powers = [0] * nineq
        if nineq and i > 0:
            # The first square is unguarded and the rest pick up exponents, so
            # `powerProduct` is actually exercised rather than always trivial.
            for k in range(nineq):
                powers[k] = rng.choice([0, 0, 1, 1, 2])
        w = rng.randint(1, max(1, cmax // 10))
        weight = "%d/%d" % (w, rng.choice([2, 3])) if (rational and i % 2) else w
        sq_specs.append({
            "weight": weight,
            "powers": powers,
            "square": rand_bundle(rng, nvars, qdeg, cmax, spec.get("qterms", 3),
                                  denominators=rational and i % 2 == 0),
        })

    p_rat = assemble(sq_specs, ineqs, eqs, mults)
    p_bundle = to_bundle(nvars, p_rat)
    if not p_bundle["terms"]:
        raise ValueError("degenerate (identically zero) target for %s" % spec["id"])

    return {
        "id": spec["id"],
        "family": spec["family"],
        "input": {"p": p_bundle, "inequalities": ineqs, "equalities": eqs},
        "certificate": {
            "terms": [{"weight": s["weight"], "powers": s["powers"],
                       "square": s["square"]} for s in sq_specs],
            "equality_multipliers": mults,
        },
    }


# The catalogue. The shapes are deliberate; the coefficients are random.
SPECS = [
    # --- 1 variable ---------------------------------------------------------
    dict(id="sos_1v_d2_tiny",   family="bench SOS",           nvars=1, qdeg=1, squares=2, cmax=3,    qterms=2),
    dict(id="sos_1v_d2_small",  family="bench SOS",           nvars=1, qdeg=1, squares=3, cmax=12,   qterms=2),
    dict(id="sos_1v_d4_small",  family="bench SOS",           nvars=1, qdeg=2, squares=2, cmax=6,    qterms=3),
    dict(id="sos_1v_d4_big",    family="bench SOS (big)",     nvars=1, qdeg=2, squares=3, cmax=900,  qterms=3),
    # --- 2 variables --------------------------------------------------------
    dict(id="sos_2v_d2_tiny",   family="bench SOS",           nvars=2, qdeg=1, squares=2, cmax=4,    qterms=3),
    dict(id="sos_2v_d2_small",  family="bench SOS",           nvars=2, qdeg=1, squares=3, cmax=15,   qterms=3),
    dict(id="sos_2v_d2_mid",    family="bench SOS",           nvars=2, qdeg=1, squares=4, cmax=40,   qterms=3),
    dict(id="sos_2v_d4_small",  family="bench SOS",           nvars=2, qdeg=2, squares=2, cmax=6,    qterms=4),
    dict(id="sos_2v_d4_mid",    family="bench SOS",           nvars=2, qdeg=2, squares=3, cmax=25,   qterms=4),
    dict(id="sos_2v_d4_big",    family="bench SOS (big)",     nvars=2, qdeg=2, squares=3, cmax=1200, qterms=4),
    dict(id="sos_2v_d2_huge",   family="bench SOS (huge)",    nvars=2, qdeg=1, squares=3, cmax=5000, qterms=3),
    dict(id="sos_2v_d4_huge",   family="bench SOS (huge)",    nvars=2, qdeg=2, squares=2, cmax=9000, qterms=4),
    # --- 3 variables --------------------------------------------------------
    dict(id="sos_3v_d2_tiny",   family="bench SOS",           nvars=3, qdeg=1, squares=2, cmax=3,    qterms=3),
    dict(id="sos_3v_d2_small",  family="bench SOS",           nvars=3, qdeg=1, squares=3, cmax=20,   qterms=4),
    dict(id="sos_3v_d2_mid",    family="bench SOS",           nvars=3, qdeg=1, squares=4, cmax=60,   qterms=4),
    dict(id="sos_3v_d4_small",  family="bench SOS",           nvars=3, qdeg=2, squares=2, cmax=7,    qterms=4),
    dict(id="sos_3v_d4_mid",    family="bench SOS",           nvars=3, qdeg=2, squares=3, cmax=30,   qterms=5),
    dict(id="sos_3v_d4_big",    family="bench SOS (big)",     nvars=3, qdeg=2, squares=3, cmax=800,  qterms=5),
    # --- equality constrained ----------------------------------------------
    dict(id="eq_2v_d2_small",   family="bench cone (eq)",     nvars=2, qdeg=1, squares=2, cmax=8,    qterms=3, eqs=1),
    dict(id="eq_2v_d2_mid",     family="bench cone (eq)",     nvars=2, qdeg=1, squares=3, cmax=30,   qterms=3, eqs=1),
    dict(id="eq_3v_d2_small",   family="bench cone (eq)",     nvars=3, qdeg=1, squares=2, cmax=10,   qterms=3, eqs=1),
    dict(id="eq_2v_d4_small",   family="bench cone (eq)",     nvars=2, qdeg=2, squares=2, cmax=9,    qterms=3, eqs=1),
    dict(id="eq_2v_d2_big",     family="bench cone (eq, big)", nvars=2, qdeg=1, squares=2, cmax=1500, qterms=3, eqs=1),
    # --- guard products -----------------------------------------------------
    dict(id="guard_2v_d2",      family="bench cone (guards)", nvars=2, qdeg=1, squares=3, cmax=6,    qterms=2, ineqs=2),
    dict(id="guard_2v_d4",      family="bench cone (guards)", nvars=2, qdeg=2, squares=3, cmax=12,   qterms=3, ineqs=2),
    dict(id="guard_3v_d2",      family="bench cone (guards)", nvars=3, qdeg=1, squares=3, cmax=9,    qterms=3, ineqs=3),
    # --- rational input, so denominators actually get cleared ---------------
    dict(id="rat_2v_d2",        family="bench SOS (rational)", nvars=2, qdeg=1, squares=3, cmax=9,   qterms=3, rational=True),
    dict(id="rat_3v_d4",        family="bench SOS (rational)", nvars=3, qdeg=2, squares=2, cmax=11,  qterms=4, rational=True),
]


# ---------------------------------------------------------------------------
# Negative controls.
# ---------------------------------------------------------------------------
def identity_holds(conv: dict) -> bool:
    """Re-run `convert`'s identity test on a (possibly perturbed) conversion."""
    lhs = [(m, Q(conv["scale"]) * Q(c)) for m, c in conv["target"]]
    rhs: list = []
    for s in conv["squares"]:
        term = [((), Q(s["weight"]))]
        for k, e in enumerate(s["powers"]):
            if k < len(conv["ineqs"]):
                term = poly_mul(term, poly_pow(
                    [(m, Q(c)) for m, c in conv["ineqs"][k]], e))
        q = [(m, Q(c)) for m, c in s["poly"]]
        term = poly_mul(term, poly_mul(q, q))
        rhs = poly_add(rhs, term)
    for h, f in zip(conv["multipliers"], conv["eqs"]):
        rhs = poly_add(rhs, poly_mul([(m, Q(c)) for m, c in h],
                                     [(m, Q(c)) for m, c in f]))
    return poly_eq(lhs, rhs)


def predicted_guards(conv: dict) -> list:
    """Which conjuncts of `Cert.check` this perturbed certificate should fail.

    Mirrors the five conjuncts of `Cert.check`. This is a PREDICTION recorded in
    the JSON so the controls can be read; the authority on the answer is the
    Lean theorem, which the kernel checks.
    """
    bad = []
    if not conv["scale"] > 0:
        bad.append("0 < scale")
    if any(s["weight"] < 0 for s in conv["squares"]):
        bad.append("every weight >= 0")
    if any(len(s["powers"]) != len(conv["ineqs"]) for s in conv["squares"]):
        bad.append("powers length == ineqs length")
    if len(conv["multipliers"]) != len(conv["eqs"]):
        bad.append("multipliers length == eqs length")
    if not identity_holds(conv):
        bad.append("the polynomial identity")
    return bad


def make_negatives(convs: dict) -> list:
    """Six ways to be wrong, each isolating one guard where that is possible."""
    out = []

    # 1. One coefficient of the target off by one. Every structural guard still
    #    passes; the identity is what fails.
    c = copy.deepcopy(convs["sos_2v_d2_small"])
    c["id"] = "neg_perturbed_target"
    m, v = c["target"][0]
    c["target"][0] = (m, v + 1)
    c["why"] = ("`sos_2v_d2_small` with one coefficient of the target increased "
                "by 1. Every structural guard still passes; the polynomial "
                "identity is what fails, by one unit in one monomial")
    out.append(c)

    # 2. A typo inside one of the squares: same target, broken witness.
    c = copy.deepcopy(convs["sos_2v_d4_mid"])
    c["id"] = "neg_perturbed_square"
    m, v = c["squares"][0]["poly"][0]
    c["squares"][0]["poly"][0] = (m, v + 1)
    c["why"] = ("`sos_2v_d4_mid` with one coefficient of the first square "
                "changed by 1. The target is untouched and still nonnegative; "
                "this certificate no longer proves it, and the checker says so "
                "rather than being talked round by a nearly-right witness")
    out.append(c)

    # 3. A negative weight on a NEGATED target, so the identity still holds and
    #    only `0 <= weight` fails.
    c = copy.deepcopy(convs["sos_1v_d2_tiny"])
    c["id"] = "neg_negative_weight"
    c["target"] = [(m, -v) for m, v in c["target"]]
    c["squares"] = [dict(s, weight=-s["weight"]) for s in c["squares"]]
    c["why"] = ("The NEGATION of `sos_1v_d2_tiny`'s target, with every weight "
                "negated too. The polynomial identity holds exactly and the "
                "arities are right; only `0 <= weight` fails. Without that "
                "guard this certificate would establish `0 <= -p` for a `p` "
                "that is a positive sum of squares")
    out.append(c)

    # 4. A negative scale, again on a negated target, so only `0 < scale` fails.
    c = copy.deepcopy(convs["sos_2v_d2_tiny"])
    c["id"] = "neg_negative_scale"
    c["target"] = [(m, -v) for m, v in c["target"]]
    c["scale"] = -c["scale"]
    c["why"] = ("The NEGATION of `sos_2v_d2_tiny`'s target with the scale "
                "negated. `scale * p = sum w q^2` still holds as an identity "
                "and every weight is still nonnegative; only `0 < scale` fails. "
                "This is the guard that stops a certificate proving the exact "
                "opposite of what it appears to")
    out.append(c)

    # 5. One multiplier too many. `dot` stops at the shorter list, so the
    #    identity is untouched and only the arity check fails.
    c = copy.deepcopy(convs["eq_2v_d2_small"])
    c["id"] = "neg_multiplier_count"
    c["multipliers"] = list(c["multipliers"]) + [[([0] * c["variables"], 7)]]
    c["why"] = ("`eq_2v_d2_small` with one extra equality multiplier and no "
                "extra constraint for it to pair with. `dot` stops at the "
                "shorter list, so the identity still holds; the arity check is "
                "what rejects it. Without that check a certificate could carry "
                "multipliers the soundness proof never looks at")
    out.append(c)

    # 6. A truncated exponent list.
    c = copy.deepcopy(convs["guard_2v_d2"])
    c["id"] = "neg_powers_length"
    c["squares"][0] = dict(c["squares"][0],
                           powers=c["squares"][0]["powers"][:-1])
    c["why"] = ("`guard_2v_d2` with one square's exponent list truncated. "
                "`powerProduct` would silently stop at the shorter list, which "
                "is exactly why the arity check exists; the truncated square "
                "carried a zero exponent, so the identity is untouched and the "
                "arity check alone rejects it")
    out.append(c)

    for c in out:
        c["family"] = "negative control"
        c["guards_failed"] = predicted_guards(c)
    return out


# ---------------------------------------------------------------------------
# Lean emission.
# ---------------------------------------------------------------------------
def def_block(conv: dict) -> list:
    """The four `def`s, in the same syntax `export_lean_cone.emit` writes."""
    name = lean_ident(conv["id"])
    L = []
    L.append("def %s_target : Poly := %s" % (name, lean_poly(conv["target"])))
    L.append("")
    L.append("def %s_ineqs : List Poly := [%s]"
             % (name, ", ".join(lean_poly(g) for g in conv["ineqs"])))
    L.append("")
    L.append("def %s_eqs : List Poly := [%s]"
             % (name, ", ".join(lean_poly(f) for f in conv["eqs"])))
    L.append("")
    L.append("def %s_cert : Cert where" % name)
    L.append("  scale := %s" % lean_int(conv["scale"]))
    if conv["squares"]:
        rows = ",\n    ".join(
            "{ weight := %s, powers := [%s], poly := %s }"
            % (lean_int(s["weight"]), ", ".join(str(e) for e in s["powers"]),
               lean_poly(s["poly"]))
            for s in conv["squares"])
        L.append("  squares := [\n    %s ]" % rows)
    else:
        L.append("  squares := []")
    L.append("  multipliers := [%s]"
             % ", ".join(lean_poly(h) for h in conv["multipliers"]))
    L.append("")
    return L


def emit_positive(conv: dict) -> str:
    return emit(conv).replace(PROTOTYPE_SENTENCE, BENCH_SENTENCE)


def emit_negative(conv: dict) -> str:
    name = lean_ident(conv["id"])
    L = []
    L.append("/-! ### `%s` --- NEGATIVE CONTROL" % conv["id"])
    L.append("")
    L.append(conv["why"] + ".")
    L.append("")
    L.append("Failing conjuncts of `Cert.check`, as predicted in Python: %s."
             % ", ".join("`%s`" % g for g in conv["guards_failed"]))
    L.append("-/")
    L.append("")
    L.extend(def_block(conv))
    L.append("/-- The checker REJECTS. The same kernel reduction as an")
    L.append("acceptance, read the other way: this is the half of the")
    L.append("measurement that a benchmark of only-passing examples cannot")
    L.append("supply. -/")
    L.append("#guard %s_cert.check %s_target %s_ineqs %s_eqs = false"
             % (name, name, name, name))
    L.append("")
    L.append("theorem %s_rejected :" % name)
    L.append("    %s_cert.check %s_target %s_ineqs %s_eqs = false := by decide"
             % (name, name, name, name))
    L.append("")
    return "\n".join(L)


BENCH_HEADER = '''import Forge.Checker.Cone
/-
  GENERATED by tools/bench_lean_cone.py. Do not edit by hand; regenerate.

  A benchmark, not a corpus. `Forge.Checker.Corpus` carries three certificates
  the prototype's search actually found; this file carries a larger family built
  the other way round -- random `q_i`, weights, guards and an equality
  constraint are chosen first, and `p := sum w_i (prod g^e) q_i^2 + h f` is
  whatever they add up to. Every target here is therefore nonnegative for a
  reason known before Lean sees it, which is what makes the file a measurement
  of the CHECKER rather than of a search.

  The point of the family is spread: one to three variables, degree 2 and 4,
  two to four squares, coefficients from single digits upwards by five orders
  of magnitude, plus equality-constrained and guard-product shapes.

  NEGATIVE CONTROLS. The `neg_*` sections are certificates that are WRONG, each
  in one specific way, and each carries a theorem that the checker returns
  `false`. A checker that accepted everything would sail through the positive
  half of this file; it would fail here.

  Everything below is checked by kernel reduction through `decide`. No
  `native_decide`, no `sorry`, no Mathlib.
-/
/- The `_concrete` proofs below are generated uniformly, so their `simp` sets
   mention lemmas that some of them do not need. Disabling the linter is
   preferable to emitting a different proof script per certificate. -/
set_option linter.unusedSimpArgs false

namespace Forge.Checker

'''

BENCH_FOOTER = "end Forge.Checker\n"


def single_check_file(conv: dict, expect: str = "true") -> str:
    """One certificate, one `decide`, nothing else -- for per-problem timing."""
    name = lean_ident(conv["id"])
    L = ["import Forge.Checker.Cone", "", "namespace Forge.Checker", ""]
    L.extend(def_block(conv))
    L.append("theorem %s_checks :" % name)
    L.append("    %s_cert.check %s_target %s_ineqs %s_eqs = %s := by decide"
             % (name, name, name, name, expect))
    L.append("")
    L.append("end Forge.Checker")
    return "\n".join(L) + "\n"


def bare_goal_file(conv: dict, tactic: str) -> str:
    """The same mathematical claim with no certificate, for `grind`/`omega`.

    `maxHeartbeats 0` is deliberate: the measurement wanted is whether the
    tactic can do it at all, bounded by wall clock, not whether it fits inside
    Lean's default deterministic budget.
    """
    n = conv["variables"]
    name = lean_ident(conv["id"])
    binders = " ".join("x%d" % i for i in range(n))
    L = ["set_option maxHeartbeats 0", ""]
    L.append("theorem %s_bare (%s : Int)" % (name, binders))
    for k, g in enumerate(conv["ineqs"]):
        L.append("    (hg%d : 0 ≤ %s)" % (k, lean_concrete(g)))
    for j, f in enumerate(conv["eqs"]):
        L.append("    (hf%d : %s = 0)" % (j, lean_concrete(f)))
    L.append("    : 0 ≤ %s := by %s" % (lean_concrete(conv["target"]), tactic))
    return "\n".join(L) + "\n"


# ---------------------------------------------------------------------------
# Running Lean.
# ---------------------------------------------------------------------------
def lean_env_vars() -> dict:
    env = dict(os.environ)
    env["LEAN_PATH"] = str(LIB)
    return env


def run_lean(path, timeout: float, cwd=LEAN_DIR) -> dict:
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(
            ["lean", str(path)], cwd=str(cwd), env=lean_env_vars(),
            capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"status": "timeout", "seconds": round(timeout, 3), "output": ""}
    except FileNotFoundError:
        return {"status": "no-lean", "seconds": 0.0, "output": "lean not on PATH"}
    dt = time.perf_counter() - t0
    out = (proc.stdout + proc.stderr).decode("utf-8", errors="replace").strip()
    return {
        "status": "ok" if proc.returncode == 0 else "fail",
        "seconds": round(dt, 3),
        "output": out,
    }


def shape(conv: dict) -> dict:
    degree = 0
    biggest = 0
    for m, c in conv["target"]:
        degree = max(degree, sum(m))
        biggest = max(biggest, abs(c))
    return {
        "variables": conv["variables"],
        "degree": degree,
        "target_terms": len(conv["target"]),
        "max_abs_coefficient": biggest,
        "squares": len(conv["squares"]),
        "inequality_constraints": len(conv["ineqs"]),
        "equality_constraints": len(conv["eqs"]),
        "scale": conv["scale"],
        "target_is_p_times": conv["p_multiplier"],
    }


LIMITATIONS = [
    "The certificates were BUILT, not found. This measures the checker and the "
    "kernel, and says nothing at all about whether a search could produce these "
    "certificates, or how long that would take. The hard half of the problem is "
    "not in this benchmark.",
    "`Forge.Checker` evaluates over `Int`, so every `_nonneg` and `_concrete` "
    "theorem is nonnegativity at INTEGER points. The polynomial identity the "
    "checker verifies holds in any commutative ring, but lifting the conclusion "
    "to the reals needs an ordered field and therefore Mathlib, which this "
    "development does not import.",
    "Problems are random within a hand-picked grid of shapes. That grid is not "
    "a distribution anyone would defend as representative of real "
    "nonnegativity goals; it was chosen to spread the parameters that plausibly "
    "drive cost.",
    "Sums of squares built from random `q_i` are generically strictly positive "
    "away from a small set, which makes them easier for a numerical or "
    "heuristic method than a tight problem with a zero at a real point would "
    "be. No hard instance (a Motzkin-style form, an SOS problem at the boundary "
    "of the cone) is in this family.",
    "Timings are single runs of the whole `lean` process on one Windows "
    "machine, including process start and `.olean` loading. The per-problem "
    "numbers subtract a measured import baseline, but there is no repetition, "
    "no warm/cold cache control and no statistics. Treat them as good to about "
    "a tenth of a second and as ratios rather than absolutes.",
    "`grind` and `omega` are given the bare goal with no certificate, which is "
    "the fair comparison for 'can core automation do this unaided' and an "
    "unfair one for the tactics themselves -- neither is designed for "
    "nonlinear real/integer arithmetic, and `omega` is documented as linear "
    "only. A failure here is a scope statement, not a defect.",
    "The tactic timeout is a wall-clock bound on a whole `lean` process. A "
    "recorded timeout means the tactic did not finish in that budget; it is "
    "not evidence that it never would.",
]


# ---------------------------------------------------------------------------
def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--seed", type=int, default=20260915)
    ap.add_argument("--out", type=Path,
                    default=LEAN_DIR / "Forge" / "Checker" / "Bench.lean")
    ap.add_argument("--json", type=Path,
                    default=ROOT / "results" / "lean-cone-benchmark.json")
    ap.add_argument("--scratch", type=Path, required=True,
                    help="directory for the throwaway per-problem Lean files")
    ap.add_argument("--tactic-timeout", type=float, default=60.0)
    ap.add_argument("--skip-timing", action="store_true",
                    help="emit the Lean file but run no measurement")
    args = ap.parse_args()

    rng = random.Random(args.seed)
    args.scratch.mkdir(parents=True, exist_ok=True)

    # --- generate and convert ----------------------------------------------
    convs = {}
    for spec in SPECS:
        record = build_record(rng, spec)
        # `convert` re-checks the integer identity in Python and raises if it
        # fails, so anything that reaches this dict is already known-good.
        convs[spec["id"]] = convert(record)

    negatives = make_negatives(convs)

    # --- write Bench.lean ---------------------------------------------------
    body = "\n".join(emit_positive(convs[s["id"]]) for s in SPECS)
    body += "\n" + "\n".join(emit_negative(c) for c in negatives)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(BENCH_HEADER + body + BENCH_FOOTER, encoding="utf-8")
    print("wrote %s (%d positive, %d negative)"
          % (args.out, len(SPECS), len(negatives)))

    if args.skip_timing:
        return 0

    # --- baselines ----------------------------------------------------------
    base_empty = args.scratch / "Baseline_empty.lean"
    base_empty.write_text("def baselineEmpty : Nat := 0\n", encoding="utf-8")
    base_import = args.scratch / "Baseline_import.lean"
    base_import.write_text("import Forge.Checker.Cone\n", encoding="utf-8")
    r_empty = run_lean(base_empty, 300.0)
    r_import = run_lean(base_import, 300.0)
    print("baseline: empty %.2fs, import %.2fs"
          % (r_empty["seconds"], r_import["seconds"]))

    # --- the whole file -----------------------------------------------------
    whole = run_lean(Path("Forge/Checker/Bench.lean"), 3600.0)
    print("Bench.lean: %s in %.2fs" % (whole["status"], whole["seconds"]))
    if whole["status"] != "ok":
        print(whole["output"][:12000])

    # --- per problem: the checker route, isolated ---------------------------
    per_problem = []
    all_convs = [convs[s["id"]] for s in SPECS] + negatives
    for conv in all_convs:
        name = lean_ident(conv["id"])
        is_neg = conv.get("family") == "negative control"
        f = args.scratch / ("Check_%s.lean" % name)
        f.write_text(single_check_file(conv, "false" if is_neg else "true"),
                     encoding="utf-8")
        r = run_lean(f, 900.0)
        row = {
            "id": conv["id"],
            "family": conv["family"],
            "kind": "negative control" if is_neg else "positive",
            "shape": shape(conv),
            "checker": {
                "status": r["status"],
                "wall_seconds": r["seconds"],
                "seconds_over_import_baseline":
                    round(r["seconds"] - r_import["seconds"], 3),
            },
        }
        if is_neg:
            row["guards_failed"] = conv["guards_failed"]
        if r["status"] != "ok":
            row["checker"]["output"] = r["output"][:2000]
        per_problem.append(row)
        print("  %-22s %-16s %6.2fs  (%s)"
              % (conv["id"], row["kind"], r["seconds"], r["status"]))

    # --- per problem: core Lean's own automation, unaided -------------------
    print("probing grind/omega (timeout %.0fs each)" % args.tactic_timeout)
    by_id = {row["id"]: row for row in per_problem}
    for conv in [convs[s["id"]] for s in SPECS]:
        name = lean_ident(conv["id"])
        row = by_id[conv["id"]]
        row["automation"] = {}
        for tactic in ("grind", "omega"):
            f = args.scratch / ("Bare_%s_%s.lean" % (tactic, name))
            f.write_text(bare_goal_file(conv, tactic), encoding="utf-8")
            r = run_lean(f, args.tactic_timeout, cwd=args.scratch)
            verdict = {"ok": "proved", "fail": "failed",
                       "timeout": "timeout"}.get(r["status"], r["status"])
            entry = {"result": verdict, "wall_seconds": r["seconds"]}
            if verdict == "failed":
                lines = [ln for ln in r["output"].splitlines() if ln.strip()]
                entry["message"] = lines[0][:300] if lines else ""
            row["automation"][tactic] = entry
            print("  %-22s %-6s %-8s %6.2fs"
                  % (conv["id"], tactic, verdict, r["seconds"]))

    # --- summary ------------------------------------------------------------
    pos = [r for r in per_problem if r["kind"] == "positive"]
    neg = [r for r in per_problem if r["kind"] == "negative control"]
    verified = sum(1 for r in pos if r["checker"]["status"] == "ok")
    rejected = sum(1 for r in neg if r["checker"]["status"] == "ok")

    def tally(tac, verdict):
        return sum(1 for r in pos
                   if r.get("automation", {}).get(tac, {}).get("result") == verdict)

    ver = subprocess.run(["lean", "--version"], capture_output=True)
    lean_version = ver.stdout.decode("utf-8", "replace").strip()

    payload = {
        "what": (
            "A measurement of the Lean cone certificate checker "
            "(Forge.Checker.Cone) on a generated family of nonnegativity "
            "problems whose certificates are known by construction, together "
            "with negative controls and a head-to-head against core Lean's own "
            "automation on the identical goals."),
        "generated_by": "tools/bench_lean_cone.py",
        "generated_lean": "lean/Forge/Checker/Bench.lean",
        "seed": args.seed,
        "lean_version": lean_version,
        "mathlib": "not used; core Lean only",
        "checked_by": "kernel reduction via `decide`; native_decide is not used",
        "totals": {
            "problems": len(per_problem),
            "positive_problems": len(pos),
            "negative_controls": len(neg),
            "positive_verified_by_checker": verified,
            "negative_controls_correctly_rejected": rejected,
            "grind_proved_unaided": tally("grind", "proved"),
            "grind_failed": tally("grind", "failed"),
            "grind_timed_out": tally("grind", "timeout"),
            "omega_proved_unaided": tally("omega", "proved"),
            "omega_failed": tally("omega", "failed"),
            "omega_timed_out": tally("omega", "timeout"),
            "tactic_timeout_seconds": args.tactic_timeout,
        },
        "wall_clock": {
            "bench_lean_whole_file_seconds": whole["seconds"],
            "bench_lean_status": whole["status"],
            "lean_startup_baseline_seconds": r_empty["seconds"],
            "import_forge_checker_cone_baseline_seconds": r_import["seconds"],
            "note": ("Per-problem checker timings are whole-process wall clock "
                     "for a one-certificate file; subtract "
                     "`import_forge_checker_cone_baseline_seconds` for the cost "
                     "attributable to the certificate itself."),
        },
        "problems": per_problem,
        "limitations": LIMITATIONS,
    }
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print("wrote %s" % args.json)
    print("verified %d/%d, rejected %d/%d, grind %d, omega %d"
          % (verified, len(pos), rejected, len(neg),
             tally("grind", "proved"), tally("omega", "proved")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
