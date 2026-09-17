#!/usr/bin/env python3
"""Export the prototype's recurrence certificates for Forge.Checker.Recurrence.

Two families are exported, and each record is re-checked twice in Python before
anything is emitted: once by the prototype's own checker (forge.io.decode.verify)
over the rationals, and once by a Python mirror of the Lean checker over the
cleared integer data. Negative controls are checked the same way, and the mirror
must reject each one on EXACTLY the conjunct it is designed to break.

WHAT THE PROTOTYPE CHECKS, AND WHAT THE EXPORT MEANS.

Polynomial recurrence -- check_recurrence(step, initial, formula).
  Variables (n, a1..ak). It verifies formula(0,a) = initial(a) and
  formula(n+1,a) - formula(n,a) = step(n,a) as polynomial identities, with
  initial free of n. The claim: the sequence F(0,a) = initial(a),
  F(n+1,a) = F(n,a) + step(n,a) equals formula(n,a) for all natural n.

  Clearing denominators. Let L > 0 clear step and initial together
  (step_Z = L*step, initial_Z = L*initial), so the integer sequence is
  F_Z = L*F. Let D > 0 be least with G = D*L*formula integral. Lean checks
  G(0,a) = D*initial_Z(a) and G(n+1,a) - G(n,a) = D*step_Z(n,a), and proves
  D * F_Z(n,a) = G(n,a). Dividing by D*L > 0 recovers F(n,a) = formula(n,a)
  exactly; conversely the prototype's identities multiplied by D*L are the Lean
  ones. Nothing is gained or lost. (In the current bundle L = 1.)

Conserved invariant -- check_invariant(InvariantCertificate(I, s0, T)).
  It verifies I(s0) = 0 and I(T(s)) = I(s) as a polynomial identity. The claim:
  I vanishes on the forward orbit {T^k(s0) : k >= 0}.

  Clearing denominators. G = D*I with D > 0 least making G integral. G = 0
  exactly where I = 0, and G o T = G iff I o T = I. The transition map and the
  initial point are NOT scaled; they must already be integral, and the exporter
  refuses otherwise (then the orbit would leave Z^d and an integer-state
  statement would not be the same claim). In the current bundle they are.

  THE PROBLEM LIVES IN "input"; THE CERTIFICATE IS THE INVARIANT ALONE. The
  initial point and transition map -- and hence the `_run` loop the user-facing
  corollary is about -- are read from the record's `input`, and the prototype's
  decoder refuses a certificate that names either.

  It was not always so. The prototype's record used to put the transition system
  inside the certificate with "input": {}, so a record could name any system its
  invariant happened to fit. An earlier version of this docstring nevertheless
  claimed "the certificate cannot choose the claim"; adversarial review showed
  that false by exporting a copy with a different initial point, which compiled.
  The data model was then fixed at its source, which is where the review said
  the fix belonged.
"""
from __future__ import annotations

import argparse
import copy
import json
import sys
from fractions import Fraction as Q
from math import lcm
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_emit_guard import validate_ids, validate_label, write_checked  # noqa: E402
# Ids and messages may be non-ASCII; the Windows console is not UTF-8.
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "prototype"))

from forge.io import decode  # noqa: E402
from forge.poly import Poly  # noqa: E402
from forge.recurrence import synthesize_recurrence  # noqa: E402

REC = "Polynomial recurrence"
INV = "Conserved invariant"


# --------------------------------------------------------------------------
# Rational polynomials as {exponent tuple: Fraction}, fixed width.
# --------------------------------------------------------------------------
def parse(obj: dict) -> tuple[int, list]:
    return obj["n"], [(tuple(m), Q(c)) for m, c in obj["terms"]]


def norm(p, width=None):
    w = width if width is not None else max([len(m) for m, _ in p], default=0)
    acc: dict = {}
    for m, c in p:
        m = tuple(m)
        if any(m[w:]):
            raise ValueError("monomial wider than the declared width")
        key = m[:w] + (0,) * (w - len(m))
        acc[key] = acc.get(key, 0) + c
    return {m: c for m, c in acc.items() if c != 0}


def eq(p, q, w) -> bool:
    return norm(p, w) == norm(q, w)


def madd(m, n):
    k = max(len(m), len(n))
    m, n = tuple(m) + (0,) * (k - len(m)), tuple(n) + (0,) * (k - len(n))
    return tuple(a + b for a, b in zip(m, n))


def pmul(p, q):
    return [(madd(m, n), a * b) for m, a in p for n, b in q]


def ppow(p, e):
    out = [((), Q(1))]
    for _ in range(e):
        out = pmul(out, p)
    return out


def psub(p, q):
    return list(p) + [(m, -c) for m, c in q]


def pscale(k, p):
    return [(m, k * c) for m, c in p]


def subst(p, qs):
    """Replace variable i by qs[i]; variables past the end become 0."""
    out = []
    for m, c in p:
        term = [((), c)]
        for i, e in enumerate(m):
            term = pmul(term, ppow(qs[i] if i < len(qs) else [], e))
        out += term
    return out


def subst_var0(p, q):
    out = []
    for m, c in p:
        if not m:
            out.append(((), c))
        else:
            out += pmul([((0,) + tuple(m[1:]), c)], ppow(q, m[0]))
    return out


def evaluate(p, point):
    total = Q(0)
    for m, c in p:
        v = c
        for i, e in enumerate(m):
            v *= (point[i] if i < len(point) else 0) ** e
        total += v
    return total


def denom(p) -> int:
    d = 1
    for _, c in p:
        d = lcm(d, Q(c).denominator)
    return d


def integral(p):
    out = []
    for m, c in p:
        assert Q(c).denominator == 1
        out.append((tuple(m), int(c)))
    return out


# --------------------------------------------------------------------------
# Python mirrors of RecCert.check and InvCert.check, conjunct by conjunct.
# --------------------------------------------------------------------------
X0_PLUS_ONE = [((1,), Q(1)), ((), Q(1))]
WIDE = 64  # isZero identifies monomials up to trailing zeros: compare wide.


def mirror_rec(scale, formula, step, initial) -> dict:
    f = [(m, Q(c)) for m, c in formula]
    s = [(m, Q(c)) for m, c in step]
    i = [(m, Q(c)) for m, c in initial]
    return {
        "scale": scale > 0,
        "initial_free_of_index": all((m[0] if m else 0) == 0 for m, _ in initial),
        "base": eq(subst_var0(f, []), pscale(scale, i), WIDE),
        "step": eq(psub(subst_var0(f, X0_PLUS_ONE), f), pscale(scale, s), WIDE),
    }


def mirror_inv(scale, invariant, initial, transition) -> dict:
    d = len(transition)
    inv = [(m, Q(c)) for m, c in invariant]
    ts = [[(m, Q(c)) for m, c in t] for t in transition]
    return {
        "scale": scale > 0,
        "nonzero": bool(norm(invariant)),
        "arity_initial": len(initial) == d,
        "arity_invariant": all(len(m) <= d for m, _ in invariant),
        "arity_transition": all(len(m) <= d for t in transition for m, _ in t),
        "base": evaluate(inv, initial) == 0,
        "step": eq(subst(inv, ts), inv, WIDE),
    }


# --------------------------------------------------------------------------
# Conversion.
# --------------------------------------------------------------------------
def convert_rec(record: dict) -> dict:
    n1, step = parse(record["input"]["step"])
    n2, initial = parse(record["input"]["initial"])
    n3, formula = parse(record["certificate"])
    if not n1 == n2 == n3:
        raise ValueError("arity mismatch in %r" % record["id"])
    L = lcm(denom(step), denom(initial))
    step_z = integral(pscale(L, step))
    init_z = integral(pscale(L, initial))
    D = denom(pscale(L, formula))
    G = integral(pscale(D * L, formula))
    return {"id": record["id"], "family": REC, "vars": n1, "input_scale": L,
            "scale": D, "formula": G, "step": step_z, "initial": init_z}


def convert_inv(record: dict) -> dict:
    c = record["certificate"]
    d, inv = parse(c["invariant"])
    # The problem comes from `input`; the certificate is the invariant alone.
    initial = [Q(v) for v in record["input"]["initial"]]
    transition = [parse(t) for t in record["input"]["transition"]]
    if any(v.denominator != 1 for v in initial):
        raise ValueError("non-integral initial point: not exportable as an Int state")
    if any(tn != d for tn, _ in transition) or any(denom(t) != 1 for _, t in transition):
        raise ValueError("transition not integral / arity mismatch")
    D = denom(inv)
    return {"id": record["id"], "family": INV, "vars": d, "scale": D,
            "invariant": integral(pscale(D, inv)),
            "initial": [int(v) for v in initial],
            "transition": [integral(t) for _, t in transition]}


# --------------------------------------------------------------------------
# Lean rendering.
# --------------------------------------------------------------------------
def lean_int(n: int) -> str:
    return "(%d)" % n if n < 0 else str(n)


def lean_poly(p) -> str:
    return "[%s]" % ", ".join("([%s], %s)" % (", ".join(map(str, m)), lean_int(c))
                              for m, c in p)


def lean_ident(s: str) -> str:
    return "".join(ch if ch.isalnum() else "_" for ch in s)


def concrete(p, names) -> str:
    """Ordinary arithmetic; monomial factors grouped and right-associated, to
    match `monoEvalFrom` (see tools/export_lean_cone.py::lean_concrete)."""
    terms = [(m, c) for m, c in p if c != 0]
    if not terms:
        return "0"
    out = []
    for k, (m, c) in enumerate(terms):
        factors = [names[i] if e == 1 else "%s^%d" % (names[i], e)
                   for i, e in enumerate(m) if e]
        grouped = None
        for f in reversed(factors):
            grouped = f if grouped is None else "%s * (%s)" % (f, grouped) \
                if " " in grouped else "%s * %s" % (f, grouped)
        a = abs(c)
        if grouped is None:
            body = str(a)
        elif a == 1:
            body = grouped if len(factors) == 1 else "(%s)" % grouped
        else:
            body = "%d * %s" % (a, grouped if len(factors) == 1 else "(%s)" % grouped)
        if k == 0:
            out.append(("-" if c < 0 else "") + body)
        else:
            out.append((" - " if c < 0 else " + ") + body)
    return "".join(out)


UNFOLD = "eval, monoEval, monoEvalFrom, setVar0, Int.pow_one, Int.pow_zero"


def emit_rec(cv: dict, python_ok: bool) -> str:
    name = lean_ident(cv["id"])
    k = cv["vars"] - 1
    params = ["a%d" % i for i in range(1, k + 1)]
    idx = "(n : Int)"
    names = [idx] + params
    D, L = cv["scale"], cv["input_scale"]
    env = ("fun i => " + "".join("if i = %d then a%d else " % (i, i) for i in range(1, k + 1))
           + "0") if k else "fun _ => 0"
    binders = " ".join(params)
    pb = "(%s : Int) " % binders if params else ""
    pa = " ".join(params)
    L_ = []
    L_.append("/-! ### `%s` --- %s, index plus %d parameter(s)" % (cv["id"], REC, k))
    L_.append("")
    L_.append("Prototype checker (`check_recurrence`) accepts: %s." % str(python_ok).lower())
    L_.append("The prototype's closed form is rational. `%s_cert.formula` is" % name)
    L_.append("`%d` times it%s. The Lean statement is" % (D * L, "" if L == 1 else
              " (input scale %d times certificate scale %d)" % (L, D)))
    L_.append("`%d * seq = formula`; since %d > 0 this says exactly that the" % (D, D))
    L_.append("sequence equals the prototype's closed form%s." %
              ("" if L == 1 else " times %d" % L))
    L_.append("-/")
    L_.append("")
    L_.append("def %s_step : Poly := %s" % (name, lean_poly(cv["step"])))
    L_.append("")
    L_.append("def %s_initial : Poly := %s" % (name, lean_poly(cv["initial"])))
    L_.append("")
    L_.append("def %s_cert : RecCert where" % name)
    L_.append("  scale := %s" % lean_int(D))
    L_.append("  formula := %s" % lean_poly(cv["formula"]))
    L_.append("")
    L_.append("/-- The checker accepts, by kernel reduction. -/")
    L_.append("theorem %s_checks : %s_cert.check %s_step %s_initial = true := by decide"
              % (name, name, name, name))
    L_.append("")
    L_.append("/-- Soundness, instantiated: every index, every parameter assignment. -/")
    L_.append("theorem %s_closed_form (a : Env) (n : Nat) :" % name)
    L_.append("    %s_cert.scale * recSeq %s_step %s_initial a n = eval (setVar0 a n) %s_cert.formula :="
              % (name, name, name, name))
    L_.append("  %s_cert.sound _ _ %s_checks a n" % (name, name))
    L_.append("")
    L_.append("/-- The sequence, written as ordinary core recursion:")
    L_.append("`seq 0 = initial`, `seq (n+1) = seq n + step n`. -/")
    L_.append("def %s_seq %s: Nat → Int" % (name, pb))
    L_.append("  | 0 => %s" % concrete(cv["initial"], names))
    L_.append("  | n + 1 => %s_seq %sn + (%s)" % (name, (pa + " ") if pa else "",
                                                 concrete(cv["step"], names)))
    L_.append("")
    L_.append("/-- The encoded sequence is the one written above. This relates two")
    L_.append("definitions; it proves nothing about the closed form. -/")
    L_.append("theorem %s_seq_eq %s: ∀ n : Nat," % (name, pb))
    L_.append("    recSeq %s_step %s_initial (%s) n = %s_seq %sn" % (
        name, name, env, name, (pa + " ") if pa else ""))
    L_.append("  | 0 => by simp [recSeq, %s_seq, %s_initial, %s] <;> omega" % (name, name, UNFOLD))
    L_.append("  | n + 1 => by")
    L_.append("    simp only [recSeq, %s_seq, %s_seq_eq %sn]" % (name, name, (pa + " ") if pa else ""))
    L_.append("    simp [%s_step, %s] <;> omega" % (name, UNFOLD))
    L_.append("")
    L_.append("/-- **The claim in ordinary arithmetic**, derived from the certificate")
    L_.append("via `%s_closed_form`; no induction on the closed form is done here. -/" % name)
    L_.append("theorem %s_concrete (n : Nat) %s:" % (name, pb))
    L_.append("    %d * %s_seq %sn = %s := by" % (D, name, (pa + " ") if pa else "",
                                              concrete(cv["formula"], names)))
    L_.append("  have h := %s_closed_form (%s) n" % (name, env))
    L_.append("  rw [%s_seq_eq] at h" % name)
    L_.append("  simp [%s_cert, %s] at h" % (name, UNFOLD))
    L_.append("  omega")
    L_.append("")
    return "\n".join(L_)


def emit_inv(cv: dict, python_ok: bool) -> str:
    name = lean_ident(cv["id"])
    d = cv["vars"]
    L_ = []
    L_.append("/-! ### `%s` --- %s, %d state variables" % (cv["id"], INV, d))
    L_.append("")
    L_.append("Prototype checker (`check_invariant`) accepts: %s." % str(python_ok).lower())
    L_.append("`%s_cert.invariant` is `%d` times the prototype's rational invariant;" % (name, cv["scale"]))
    L_.append("since %d > 0 it vanishes exactly where the rational one does. The" % cv["scale"])
    L_.append("initial point and the transition map are integral and are not scaled.")
    L_.append("-/")
    L_.append("")
    L_.append("def %s_initial : List Int := [%s]" % (name, ", ".join(map(lean_int, cv["initial"]))))
    L_.append("")
    L_.append("def %s_transition : List Poly :=" % name)
    L_.append("  [%s]" % ",\n   ".join(lean_poly(t) for t in cv["transition"]))
    L_.append("")
    L_.append("def %s_cert : InvCert where" % name)
    L_.append("  scale := %s" % lean_int(cv["scale"]))
    L_.append("  invariant := %s" % lean_poly(cv["invariant"]))
    L_.append("")
    L_.append("/-- The checker accepts, by kernel reduction. -/")
    L_.append("theorem %s_checks :" % name)
    L_.append("    %s_cert.check %s_initial %s_transition = true := by decide" % (name, name, name))
    L_.append("")
    L_.append("/-- Soundness, instantiated: the invariant holds at EVERY reachable state. -/")
    L_.append("theorem %s_invariant (s : Env)" % name)
    L_.append("    (hs : Reachable %s_transition (pointEnv %s_initial) s) :" % (name, name))
    L_.append("    eval s %s_cert.invariant = 0 :=" % name)
    L_.append("  %s_cert.sound _ _ %s_checks s hs" % (name, name))
    L_.append("")
    if d != 2:
        L_.append("-- No ordinary-arithmetic corollary: the exporter only renders 2-state loops.")
        L_.append("")
        return "\n".join(L_)
    run = "(%s_run k)" % name
    names = [run + ".1", run + ".2"]
    L_.append("/-- The loop, written as ordinary core recursion on a pair. -/")
    L_.append("def %s_run : Nat → Int × Int" % name)
    L_.append("  | 0 => (%s, %s)" % tuple(map(lean_int, cv["initial"])))
    L_.append("  | k + 1 => (%s,\n      %s)" % tuple(concrete(t, names) for t in cv["transition"]))
    L_.append("")
    L_.append("/-- Every state of the loop is reachable. Relates definitions only. -/")
    L_.append("theorem %s_run_reachable : ∀ k : Nat," % name)
    L_.append("    Reachable %s_transition (pointEnv %s_initial) (pairEnv (%s_run k))" % (name, name, name))
    L_.append("  | 0 => by")
    L_.append("    have e : pairEnv (%s_run 0) = pointEnv %s_initial := by" % (name, name))
    L_.append("      funext i")
    L_.append("      match i with")
    L_.append("      | 0 => simp [pairEnv, pointEnv, %s_initial, %s_run]" % (name, name))
    L_.append("      | 1 => simp [pairEnv, pointEnv, %s_initial, %s_run]" % (name, name))
    L_.append("      | i + 2 => simp [pairEnv, pointEnv, %s_initial]" % name)
    L_.append("    rw [e]")
    L_.append("    exact .init")
    L_.append("  | k + 1 => by")
    L_.append("    have h := Reachable.step (%s_run_reachable k)" % name)
    L_.append("    have e : substEnv (pairEnv (%s_run k)) %s_transition = pairEnv (%s_run (k + 1)) := by"
              % (name, name, name))
    L_.append("      funext i")
    L_.append("      match i with")
    for i in (0, 1):
        L_.append("      | %d =>" % i)
        L_.append("        simp [substEnv, pairEnv, %s_transition, %s_run, %s] <;> omega"
                  % (name, name, UNFOLD))
    L_.append("      | i + 2 => simp [substEnv, pairEnv, %s_transition, eval]" % name)
    L_.append("    rwa [e] at h")
    L_.append("")
    L_.append("/-- **The claim in ordinary arithmetic**: at every iterate `(x0, x1)` of the")
    L_.append("loop, the (scaled) invariant vanishes. Derived from `%s_invariant`. -/" % name)
    L_.append("theorem %s_concrete (k : Nat) (x0 x1 : Int) (h : %s_run k = (x0, x1)) :" % (name, name))
    L_.append("    %s = 0 := by" % concrete(cv["invariant"], ["x0", "x1"]))
    L_.append("  have hr := %s_invariant _ (%s_run_reachable k)" % (name, name))
    L_.append("  rw [h] at hr")
    L_.append("  simp [%s_cert, pairEnv, %s] at hr" % (name, UNFOLD))
    L_.append("  omega")
    L_.append("")
    return "\n".join(L_)


# --------------------------------------------------------------------------
# Negative controls.
# --------------------------------------------------------------------------
def negatives_rec(records: dict) -> list:
    """(label, record-or-None, converted, conjunct expected to fail)."""
    out = []
    for rid, r in records.items():
        for j, bad in enumerate(decode.mutations(r)):
            out.append(("%s_bundle_mutation_%d" % (rid, j), bad, convert_rec(bad), "base",
                        "the bundle's own mutation: constant 1 appended to the closed form (times the scale)"))
    # Off by one: sum over i <= n instead of i < n.
    r = copy.deepcopy(records["power_sum_1"])
    r["certificate"] = {"n": 1, "terms": [[[1], "1/2"], [[2], "1/2"]]}
    out.append(("power_sum_1_off_by_one", r, convert_rec(r), "step",
                "closed form of sum_{i<=n} i, not sum_{i<n} i"))
    # Right closed form, wrong recurrence.
    r = copy.deepcopy(records["power_sum_2"])
    r["input"]["step"] = {"n": 1, "terms": [[[3], "1"]]}
    out.append(("power_sum_2_wrong_step", r, convert_rec(r), "step",
                "power_sum_2's closed form offered for the step n^3"))
    # Vacuous scale: 0 * seq = 0 holds for every sequence.
    cv = convert_rec(records["power_sum_1"])
    cv = dict(cv, scale=0, formula=[])
    out.append(("power_sum_1_zero_scale", None, cv, "scale",
                "scale 0 and formula 0: both identities hold, the claim would be vacuous"))
    # Initial value syntactically mentioning the index (with coefficient 0, so
    # both identities still hold). Integer-level only: the prototype's Poly
    # normalises zero coefficients away, so it cannot express this input.
    cv = convert_rec(records["power_sum_0"])
    cv = dict(cv, initial=[((1,), 0)])
    out.append(("power_sum_0_initial_mentions_index", None, cv, "initial_free_of_index",
                "initial value [([1], 0)] names the index variable"))
    return out


def negatives_inv(record: dict) -> list:
    out = []
    for j, bad in enumerate(decode.mutations(record)):
        out.append(("%s_bundle_mutation_%d" % (record["id"], j), bad, convert_inv(bad), "base",
                    "the bundle's own mutation: constant 1 appended to the invariant (times the scale)"))
    cv = dict(convert_inv(record), invariant=[])
    out.append(("%s_zero_invariant" % record["id"], None, cv, "nonzero",
                "the zero polynomial: vanishes everywhere and is preserved by every map"))
    cv = dict(convert_inv(record), scale=0)
    out.append(("%s_zero_scale" % record["id"], None, cv, "scale",
                "scale 0: the invariant is unchanged, only the positivity conjunct fails"))
    if record["id"] != "cubic_accumulator":
        # The perturbations below are written for cubic_accumulator's shape (a
        # 2-state system whose second transition has a constant term). Applying
        # them to other records crashed the exporter; they are now scoped.
        return out
    r = copy.deepcopy(record)
    r["input"]["transition"][1]["terms"][0][1] = "2"   # s' = s + (n+1)^3 + 1
    assert r["input"]["transition"][1]["terms"][0][0] == [0, 0]
    out.append(("%s_perturbed_transition" % record["id"], r, convert_inv(r), "step",
                "transition s' = s + (n+1)^3 + 1: not conserved"))
    r = copy.deepcopy(record)
    r["input"]["initial"] = ["0", "1"]
    out.append(("%s_wrong_initial" % record["id"], r, convert_inv(r), "base",
                "initial point (0, 1): invariant is -4 there, not 0"))
    r = copy.deepcopy(record)
    r["input"]["initial"] = ["0"]
    out.append(("%s_short_initial" % record["id"], r, convert_inv(r), "arity_initial",
                "initial point of dimension 1 for a 2-state system"))
    return out


def check_negative(kind, label, rec, cv, conjunct):
    try:
        py = decode.verify(rec) if rec is not None else None
    except decode.DecodeError:
        # The prototype's decoder refusing a malformed mutation IS a rejection.
        # (Before this, a closed form with a constant term crashed the exporter:
        # decode.mutations appends a constant monomial, which duplicates it.)
        py = False
    if py is True:
        raise AssertionError("%s: the prototype ACCEPTS a negative control" % label)
    if kind == REC:
        m = mirror_rec(cv["scale"], cv["formula"], cv["step"], cv["initial"])
    else:
        m = mirror_inv(cv["scale"], cv["invariant"], cv["initial"], cv["transition"])
    failing = sorted(k for k, v in m.items() if not v)
    if failing != [conjunct]:
        raise AssertionError("%s: expected exactly %r to fail, got %r" % (label, conjunct, failing))
    return py, failing


HEADER = '''import Forge.Checker.Recurrence
/-
  GENERATED by tools/export_lean_recurrence.py from the prototype's certificate
  bundle (prototype/results/certificates.json). Do not edit by hand; regenerate.

  Families: "Polynomial recurrence" (every record) and "Conserved invariant"
  (every record). Each certificate was re-checked in Python by the prototype's
  own checker over the rationals and by a mirror of the Lean checker over the
  cleared integers, then checked here by kernel reduction (`decide`).
  No `native_decide`.

  Every `_concrete` theorem is derived FROM the certificate's soundness theorem.
  The `_seq_eq` / `_run_reachable` lemmas only identify the encoded sequence or
  state space with an ordinary core-recursive definition; they contain no
  arithmetic about the closed form or the invariant.
-/
set_option linter.unusedSimpArgs false

namespace Forge.Checker

/-- A pair of integers as a state. -/
def pairEnv (p : Int × Int) : Env := fun i => if i = 0 then p.1 else if i = 1 then p.2 else 0

'''

FOOTER = "end Forge.Checker\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--bundle", type=Path,
                    default=ROOT / "prototype" / "results" / "certificates.json")
    ap.add_argument("--out", type=Path,
                    default=ROOT / "lean" / "Forge" / "Checker" / "RecurrenceCorpus.lean")
    ap.add_argument("--json", type=Path,
                    default=ROOT / "results" / "lean-recurrence-corpus.json")
    args = ap.parse_args()

    records = json.loads(args.bundle.read_text(encoding="utf-8"))
    # Ids are interpolated into generated Lean: refuse, never escape. This also
    # refuses duplicates, which the dict below would otherwise collapse silently.
    validate_ids([r["id"] for r in records if r["family"] in (REC, INV)])
    recs = {r["id"]: r for r in records if r["family"] == REC}
    invs = [r for r in records if r["family"] == INV]
    if not recs or not invs:
        raise SystemExit("recurrence families missing from the bundle")

    chunks, summary, negs = [], [], []

    for r in recs.values():
        ok = decode.verify(r)
        if ok is not True:
            raise SystemExit("prototype rejects %s" % r["id"])
        cv = convert_rec(r)
        m = mirror_rec(cv["scale"], cv["formula"], cv["step"], cv["initial"])
        if not all(m.values()):
            raise SystemExit("integer re-check failed for %s: %r" % (r["id"], m))
        chunks.append(emit_rec(cv, ok))
        summary.append({"id": cv["id"], "family": REC, "scale": cv["scale"],
                        "input_scale": cv["input_scale"], "source": "bundle"})

    # A multivariate positive control, synthesised by the prototype's own search
    # (not in the bundle): F(0,a) = a, F(n+1,a) = F(n,a) + a.
    a = Poly.var(2, 1)
    f = synthesize_recurrence(a, a)
    synth = {"id": "param_linear_control", "family": REC,
             "input": {"step": a.json(), "initial": a.json()}, "certificate": f.json()}
    ok = decode.verify(synth)
    cv = convert_rec(synth)
    if ok is not True or not all(mirror_rec(cv["scale"], cv["formula"], cv["step"],
                                            cv["initial"]).values()):
        raise SystemExit("synthetic multivariate control failed")
    chunks.append(emit_rec(cv, ok))
    summary.append({"id": cv["id"], "family": REC, "scale": cv["scale"],
                    "input_scale": cv["input_scale"],
                    "source": "synthesize_recurrence (not in bundle)"})

    for r in invs:
        ok = decode.verify(r)
        if ok is not True:
            raise SystemExit("prototype rejects %s" % r["id"])
        cv = convert_inv(r)
        m = mirror_inv(cv["scale"], cv["invariant"], cv["initial"], cv["transition"])
        if not all(m.values()):
            raise SystemExit("integer re-check failed for %s: %r" % (r["id"], m))
        chunks.append(emit_inv(cv, ok))
        summary.append({"id": cv["id"], "family": INV, "scale": cv["scale"], "source": "bundle"})

    # --- negative controls ---------------------------------------------------
    N = ["/-! ### Negative controls",
         "",
         "Each must be REJECTED. The exporter checked, before emitting, that the",
         "prototype rejects it (where the prototype can express it) and that the",
         "mirror of the Lean checker fails on exactly the conjunct named. -/",
         ""]
    for label, rec, cv, conj, why in negatives_rec(recs):
        py, _ = check_negative(REC, label, rec, cv, conj)
        nm = lean_ident(label)
        N.append("/-- %s. Breaks: `%s`. Prototype: %s. -/" % (
            why, conj, "rejects" if py is False else "cannot express"))
        N.append("theorem %s_rejected :" % nm)
        N.append("    ({ scale := %s, formula := %s } : RecCert).check %s %s = false := by decide"
                 % (lean_int(cv["scale"]), lean_poly(cv["formula"]),
                    lean_poly(cv["step"]), lean_poly(cv["initial"])))
        N.append("")
        negs.append({"label": label, "family": REC, "breaks": conj,
                     "prototype": "rejects" if py is False else "not expressible"})
    for r in invs:
        for label, rec, cv, conj, why in negatives_inv(r):
            py, _ = check_negative(INV, label, rec, cv, conj)
            nm = lean_ident(label)
            N.append("/-- %s. Breaks: `%s`. Prototype: %s. -/" % (
                why, conj, "rejects" if py is False else "cannot express"))
            N.append("theorem %s_rejected :" % nm)
            N.append("    ({ scale := %s, invariant := %s } : InvCert).check [%s]"
                     % (lean_int(cv["scale"]), lean_poly(cv["invariant"]),
                        ", ".join(map(lean_int, cv["initial"]))))
            N.append("      [%s] = false := by decide"
                     % ", ".join(lean_poly(t) for t in cv["transition"]))
            N.append("")
            negs.append({"label": label, "family": INV, "breaks": conj,
                         "prototype": "rejects" if py is False else "not expressible"})

    write_checked(args.out, HEADER + "\n".join(chunks) + "\n" + "\n".join(N) + "\n" + FOOTER)
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps({
        "what": ("Recurrence-family certificates (Polynomial recurrence, Conserved "
                 "invariant) exported to Forge.Checker.Recurrence with denominators "
                 "cleared; re-checked in Python by the prototype checker and by a "
                 "mirror of the Lean checker, then by the Lean kernel."),
        "generated_lean": "lean/Forge/Checker/RecurrenceCorpus.lean",
        "checked_by": "kernel reduction via `decide`; native_decide is not used",
        "certificates": summary,
        "negative_controls": negs,
    }, indent=2) + "\n", encoding="utf-8")
    print("wrote %s" % args.out)
    print("positive: %d, negative: %d" % (len(summary), len(negs)))
    for s in summary:
        print("  + %-24s scale=%s" % (s["id"], s["scale"]))
    for n in negs:
        print("  - %-48s breaks=%-22s prototype=%s" % (n["label"], n["breaks"], n["prototype"]))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
