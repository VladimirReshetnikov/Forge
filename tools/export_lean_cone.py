#!/usr/bin/env python3
"""Export the prototype's cone certificates as Lean terms for Forge.Checker.Cone.

The prototype works over the rationals. The Lean checker works over `Int`,
because `Int` is in Lean core and `Rat`'s arithmetic lemmas largely are not, and
every Mathlib-importing file in this repository is unchecked. Clearing
denominators is therefore not a convenience -- it is what lets the result be
checked at all.

THE TRANSFORMATION. A certificate asserts, over the rationals,

    p = sum_i w_i * (prod_k g_k ^ e_ik) * q_i^2  +  sum_j h_j * f_j

Write P = dp*p, G_k = dg_k*g_k, F_j = df_j*f_j, Q_i = dq_i*q_i, H_j = dh_j*h_j
for the least positive integer multipliers that clear each polynomial. Then

    alpha_i = w_i / (prod_k dg_k^e_ik * dq_i^2)      (rational, >= 0)
    beta_j  = 1 / (dh_j * df_j)                      (rational, > 0)

and p = sum_i alpha_i * (prod G_k^e_ik) * Q_i^2 + sum_j beta_j * H_j * F_j.
Multiplying by any common denominator M of the alpha_i and beta_j that is also
a multiple of dp gives the integer identity the Lean checker verifies:

    (M/dp) * P = sum_i (M*alpha_i) * (prod G_k^e_ik) * Q_i^2
               + sum_j ((M*beta_j) * H_j) * F_j

All the hypotheses transfer exactly, because every multiplier is POSITIVE:
G_k >= 0 iff g_k >= 0, F_j = 0 iff f_j = 0, and P >= 0 iff p >= 0.

This script verifies the integer identity in Python before emitting anything. A
failure here is a defect in this script, not a rejected certificate, and it
raises rather than emitting a file Lean would reject.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as Q
from math import lcm
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_emit_guard import validate_ids, validate_label, write_checked  # noqa: E402
# Ids and messages may be non-ASCII; the Windows console is not UTF-8.
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

ROOT = Path(__file__).resolve().parents[1]

Mono = tuple
RatPoly = list      # [(mono, Fraction)]
IntPoly = list      # [(mono, int)]


# --------------------------------------------------------------------------
# Rational polynomial arithmetic, enough to re-check the identity here.
# --------------------------------------------------------------------------
def parse_poly(obj: dict) -> RatPoly:
    return [(tuple(mono), Q(coeff)) for mono, coeff in obj["terms"]]


def poly_add(a, b):
    return list(a) + list(b)


def mono_add(m, n):
    width = max(len(m), len(n))
    m = tuple(m) + (0,) * (width - len(m))
    n = tuple(n) + (0,) * (width - len(n))
    return tuple(x + y for x, y in zip(m, n))


def poly_mul(a, b):
    return [(mono_add(m, n), c * d) for m, c in a for n, d in b]


def poly_scale(k, a):
    return [(m, k * c) for m, c in a]


def poly_pow(a, e):
    out = [((), Q(1))]
    for _ in range(e):
        out = poly_mul(out, a)
    return out


def normalise(a):
    """Collect like terms, drop zeros, and pad monomials to a common width."""
    width = max([len(m) for m, _ in a], default=0)
    acc: dict = {}
    for m, c in a:
        key = tuple(m) + (0,) * (width - len(m))
        acc[key] = acc.get(key, 0) + c
    return {m: c for m, c in acc.items() if c != 0}


def poly_eq(a, b) -> bool:
    return normalise(a) == normalise(b)


def clear_denominators(a: RatPoly) -> tuple[IntPoly, int]:
    """Return an integer polynomial and the positive multiplier used."""
    d = 1
    for _, c in a:
        d = lcm(d, c.denominator)
    out = []
    for m, c in a:
        scaled = c * d
        assert scaled.denominator == 1
        out.append((m, int(scaled)))
    return out, d


# --------------------------------------------------------------------------
# The transformation.
# --------------------------------------------------------------------------
def convert(record: dict) -> dict:
    inp = record["input"]
    cert = record["certificate"]

    p_rat = parse_poly(inp["p"])
    ineq_rat = [parse_poly(g) for g in inp.get("inequalities", [])]
    eq_rat = [parse_poly(f) for f in inp.get("equalities", [])]

    P, dp = clear_denominators(p_rat)
    Gs, dgs = zip(*[clear_denominators(g) for g in ineq_rat]) if ineq_rat else ((), ())
    Fs, dfs = zip(*[clear_denominators(f) for f in eq_rat]) if eq_rat else ((), ())
    Gs, dgs, Fs, dfs = list(Gs), list(dgs), list(Fs), list(dfs)

    squares = []
    for term in cert["terms"]:
        weight = Q(term["weight"])
        if weight < 0:
            raise ValueError("a square carries a negative weight")
        powers = list(term.get("powers", []))
        if len(powers) != len(Gs):
            # The prototype omits trailing zero exponents.
            powers = powers + [0] * (len(Gs) - len(powers))
        Qi, dq = clear_denominators(parse_poly(term["square"]))
        divisor = dq * dq
        for k, e in enumerate(powers):
            divisor *= dgs[k] ** e
        squares.append({"alpha": weight / divisor, "powers": powers, "poly": Qi})

    multipliers = []
    for j, h in enumerate(cert.get("equality_multipliers", [])):
        Hj, dh = clear_denominators(parse_poly(h))
        multipliers.append({"beta": Q(1, dh * dfs[j]), "poly": Hj})
    if len(multipliers) != len(Fs):
        raise ValueError("multiplier count does not match the equality constraints")

    # M: a common denominator for every alpha and beta, and a multiple of dp.
    M = dp
    for s in squares:
        M = lcm(M, s["alpha"].denominator)
    for m in multipliers:
        M = lcm(M, m["beta"].denominator)

    scale = M // dp
    assert scale * dp == M and scale > 0

    out_squares = []
    for s in squares:
        w = s["alpha"] * M
        assert w.denominator == 1 and w >= 0
        out_squares.append({"weight": int(w), "powers": s["powers"], "poly": s["poly"]})

    out_multipliers = []
    for m in multipliers:
        factor = m["beta"] * M
        assert factor.denominator == 1
        out_multipliers.append(poly_scale(int(factor), m["poly"]))

    # --- re-check the integer identity before emitting anything -------------
    lhs = poly_scale(Q(scale), [(m, Q(c)) for m, c in P])
    rhs: RatPoly = []
    for s, spec in zip(out_squares, squares):
        term = [((), Q(s["weight"]))]
        for k, e in enumerate(s["powers"]):
            term = poly_mul(term, poly_pow([(m, Q(c)) for m, c in Gs[k]], e))
        q = [(m, Q(c)) for m, c in s["poly"]]
        term = poly_mul(term, poly_mul(q, q))
        rhs = poly_add(rhs, term)
    for Hj, Fj in zip(out_multipliers, Fs):
        rhs = poly_add(rhs, poly_mul([(m, Q(c)) for m, c in Hj],
                                     [(m, Q(c)) for m, c in Fj]))
    if not poly_eq(lhs, rhs):
        raise ValueError("integer identity failed for %r" % record["id"])

    return {
        "id": record["id"],
        "family": record["family"],
        "variables": inp["p"]["n"],
        "p_multiplier": dp,
        "target": P,
        "ineqs": Gs,
        "eqs": Fs,
        "scale": scale,
        "squares": out_squares,
        "multipliers": out_multipliers,
    }


# --------------------------------------------------------------------------
# Lean emission.
# --------------------------------------------------------------------------
def lean_int(n: int) -> str:
    return "(%d)" % n if n < 0 else str(n)


def lean_poly(p: IntPoly) -> str:
    if not p:
        return "[]"
    terms = ", ".join("([%s], %s)" % (", ".join(str(e) for e in m), lean_int(c))
                      for m, c in p)
    return "[%s]" % terms


def lean_concrete(poly: IntPoly) -> str:
    """An integer polynomial as ordinary Lean arithmetic over `x0, x1, ...`.

    Two association details, both of which cost a failed compile to find.

    The factors of a monomial are GROUPED: `(-26) * (x0 * x1)` and not
    `(-26) * x0 * x1`. The ungrouped form parses as `((-26) * x0) * x1`, which
    `omega` sees as an atom unrelated to the `x0 * x1` in the unfolded
    hypothesis.

    And within the group they are associated to the RIGHT: `x0 * (x1 * x2)`
    and not `x0 * x1 * x2`. `monoEvalFrom` recurses on the tail, so it builds
    `x i ^ e * (rest)`, right-associated; the flat form parses to the left and
    `omega` again sees two unrelated atoms. This is invisible for monomials of
    at most two factors, where the two associations coincide -- which is every
    monomial in the current corpus, and is why it went unnoticed until a
    three-variable benchmark hit it.
    """
    if not poly:
        return "0"
    parts = []
    for mono, c in poly:
        factors = []
        for i, e in enumerate(mono):
            if e == 0:
                continue
            factors.append("x%d" % i if e == 1 else "x%d^%d" % (i, e))
        coeff = "(%d)" % c if c < 0 else str(c)
        if not factors:
            parts.append(coeff)
        elif len(factors) == 1:
            parts.append("%s * %s" % (coeff, factors[0]))
        else:
            # Right-associated, to match monoEvalFrom's recursion on the tail.
            grouped = factors[-1]
            for f in reversed(factors[:-1]):
                grouped = "%s * (%s)" % (f, grouped) if " " in grouped                     else "%s * %s" % (f, grouped)
            parts.append("%s * (%s)" % (coeff, grouped))
    return " + ".join(parts)


def lean_env(nvars: int) -> str:
    """`fun i => if i = 0 then x0 else if i = 1 then x1 else 0`."""
    if nvars == 0:
        return "fun _ => 0"
    body = "0"
    for i in reversed(range(nvars)):
        body = "if i = %d then x%d else %s" % (i, i, body)
    return "fun i => %s" % body


UNFOLD = "eval, monoEval, monoEvalFrom, Int.pow_one, Int.pow_zero"


def lean_ident(s: str) -> str:
    return "".join(ch if ch.isalnum() else "_" for ch in s)


HEADER = '''import Forge.Checker.Cone
/-
  GENERATED by tools/export_lean_cone.py from the prototype's certificate
  bundle. Do not edit by hand; regenerate.

  Every certificate below was produced by the Python search in
  prototype/forge/cone.py and prototype/forge/quadratic.py, over the rationals.
  The exporter cleared denominators, re-checked the resulting integer identity
  in Python, and emitted it here. The Lean kernel then checks it again by
  reduction, with no appeal to the compiler and no `native_decide`.

  This file is the loop the project is named for, closed once: a certificate a
  search produced, checked by Lean, with a proof that checking it establishes
  the mathematical claim.
-/
/- The `_concrete` proofs below are generated uniformly, so their `simp` sets
   mention lemmas that some of them do not need. Disabling the linter is
   preferable to emitting a different proof script per certificate. -/
set_option linter.unusedSimpArgs false

namespace Forge.Checker

'''

FOOTER = "end Forge.Checker\n"


def emit(conv: dict) -> str:
    name = lean_ident(conv["id"])
    dp = conv["p_multiplier"]
    L = []
    L.append("/-! ### `%s` --- %s, %d variables"
             % (conv["id"], conv["family"], conv["variables"]))
    L.append("")
    L.append("The prototype's certificate is over the rationals. `%s_target` is"
             % name)
    if dp == 1:
        L.append("the original `p`, whose coefficients were already integers.")
    else:
        L.append("`%d * p`, the least positive integer multiple of the original" % dp)
        L.append("`p`. Since %d > 0, the target is nonnegative exactly where `p` is."
                 % dp)
    if conv["ineqs"] or conv["eqs"]:
        L.append("")
        L.append("The constraints are cleared the same way and by positive")
        L.append("multipliers, so the hypotheses below say exactly what the")
        L.append("original constraints say.")
    L.append("-/")
    L.append("")
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
    L.append("/-- The checker accepts. `decide` elaborates the `Bool` and the")
    L.append("kernel replays the reduction, so this rests on the kernel alone. -/")
    L.append("theorem %s_checks :" % name)
    L.append("    %s_cert.check %s_target %s_ineqs %s_eqs = true := by decide"
             % (name, name, name, name))
    L.append("")

    hyps, args = [], []
    if conv["ineqs"]:
        hyps.append("    (hg : ∀ g ∈ %s_ineqs, 0 ≤ eval x g)" % name)
        args.append("hg")
    else:
        args.append("(by simp [%s_ineqs])" % name)
    if conv["eqs"]:
        hyps.append("    (hz : ∀ f ∈ %s_eqs, eval x f = 0)" % name)
        args.append("hz")
    else:
        args.append("(by simp [%s_eqs])" % name)

    L.append("/-- Nonnegativity at every assignment satisfying the constraints.")
    L.append("Follows from the check by `Cert.sound`; no arithmetic is repeated")
    L.append("here and no property of the search is assumed. -/")
    L.append("theorem %s_nonneg (x : Env)" % name)
    L.extend(hyps)
    L.append("    : 0 ≤ eval x %s_target :=" % name)
    L.append("  %s_cert.sound _ _ _ %s_checks x %s"
             % (name, name, " ".join(args)))
    L.append("")

    # --- the bridge to a goal a person would actually type ------------------
    n = conv["variables"]
    binders = " ".join("x%d" % i for i in range(n))
    chyps = []
    for k, g in enumerate(conv["ineqs"]):
        chyps.append("    (hg%d : 0 \u2264 %s)" % (k, lean_concrete(g)))
    for j, f in enumerate(conv["eqs"]):
        chyps.append("    (hf%d : %s = 0)" % (j, lean_concrete(f)))

    cargs = []
    if conv["ineqs"]:
        cargs.append("""(by
    intro g hg
    simp [%s_ineqs] at hg
    rcases hg with %s <;>
      simp [%s] <;> omega)""" % (name, " | ".join(["rfl"] * len(conv["ineqs"])), UNFOLD))
    if conv["eqs"]:
        if len(conv["eqs"]) == 1:
            cargs.append("""(by
    intro f hf
    simp [%s_eqs] at hf
    subst hf
    simp [%s]
    omega)""" % (name, UNFOLD))
        else:
            cargs.append("""(by
    intro f hf
    simp [%s_eqs] at hf
    rcases hf with %s <;>
      simp [%s] <;> omega)""" % (name, " | ".join(["rfl"] * len(conv["eqs"])), UNFOLD))

    L.append("/-- The same fact as `%s_nonneg`, stated in ordinary arithmetic." % name)
    L.append("This is the form a goal actually arrives in; the encoding above is")
    L.append("an implementation detail of the checker, not something to state. -/")
    L.append("theorem %s_concrete (%s : Int)" % (name, binders))
    L.extend(chyps)
    L.append("    : 0 \u2264 %s := by" % lean_concrete(conv["target"]))
    L.append("  have h := %s_nonneg (%s) %s" % (name, lean_env(n), " ".join(cargs)))
    L.append("  simp [%s_target, %s] at h" % (name, UNFOLD))
    L.append("  omega")
    L.append("")
    return "\n".join(L)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--bundle", type=Path,
                    default=ROOT / "prototype" / "results" / "certificates.json")
    ap.add_argument("--out", type=Path,
                    default=ROOT / "lean" / "Forge" / "Checker" / "Corpus.lean")
    ap.add_argument("--json", type=Path,
                    default=ROOT / "results" / "lean-cone-corpus.json")
    args = ap.parse_args()

    records = json.loads(args.bundle.read_text(encoding="utf-8"))
    wanted = [r for r in records
              if r["family"] in ("Quadratic SOS", "Finite cone LP")]
    # Ids and families are interpolated into generated Lean: refuse, never escape.
    validate_ids([r["id"] for r in wanted])
    for r in wanted:
        validate_label(r["family"], {"Quadratic SOS", "Finite cone LP"}, "family")
    if not wanted:
        raise SystemExit("no cone certificates in the bundle")

    converted = [convert(r) for r in wanted]

    args.out.parent.mkdir(parents=True, exist_ok=True)
    write_checked(args.out, HEADER + "\n".join(emit(c) for c in converted) + FOOTER)

    summary = []
    for c in converted:
        summary.append({
            "id": c["id"],
            "family": c["family"],
            "variables": c["variables"],
            "target_is_p_times": c["p_multiplier"],
            "scale": c["scale"],
            "squares": len(c["squares"]),
            "multipliers": len(c["multipliers"]),
            "inequality_constraints": len(c["ineqs"]),
            "equality_constraints": len(c["eqs"]),
        })
    args.json.write_text(json.dumps({
        "what": ("Every cone certificate in the prototype bundle, converted from "
                 "rational to integer form for Forge.Checker.Cone. The integer "
                 "identity is re-checked in Python before emission and again by "
                 "the Lean kernel when Corpus.lean is elaborated."),
        "generated_lean": "lean/Forge/Checker/Corpus.lean",
        "checked_by": "kernel reduction via `decide`; native_decide is not used",
        "certificates": summary,
    }, indent=2) + "\n", encoding="utf-8")

    print("wrote %s" % args.out)
    print("converted %d certificates" % len(converted))
    for c in summary:
        print("  %-24s scale=%-6d squares=%d multipliers=%d ineqs=%d eqs=%d"
              % (c["id"], c["scale"], c["squares"], c["multipliers"],
                 c["inequality_constraints"], c["equality_constraints"]))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
