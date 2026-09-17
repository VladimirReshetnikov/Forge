#!/usr/bin/env python3
"""Export the prototype's integral affine witnesses for Forge.Checker.Affine.

WHAT IS CERTIFIED. For the bundle family "Integral affine witness",
prototype/forge/io/decode.py calls

    check_affine_witness(A, B, c, AffineWitness(linear, offset), True)

and the final True is `require_integral`: every entry of `linear` (W, k x p) and
`offset` (d, length k) must have denominator 1. With the shape conditions of
`_shape` it accepts exactly when W and d are integral and A W = B, A d = c over
the rationals; equivalently, for every x the integer vector w(x) = W x + d solves
A w = B x + c.

NO DENOMINATORS ARE CLEARED. An accepted certificate is integral by definition,
so it is emitted verbatim as `Int`. The inputs A, B, c are required to be JSON
integers (the prototype would also accept rational strings; this exporter
refuses them rather than rescale, because rescaling A would change which
integral W, d solve the system). For integer data the rational identities hold
iff the integer identities do, since Int -> Q is an injective ring map.

WHAT THIS SCRIPT CHECKS BEFORE EMITTING, for every positive and negative case:
  1. the prototype's own `check_affine_witness(..., True)`,
  2. an independent integer re-implementation of the Lean `AffineCert.check`
     (same truncating `dot`, same `comb`, same shape test),
and it raises unless the two verdicts agree and match the expectation. For each
negative control it also records which of the Lean checker's two halves
(`shapeOK`, `rowsOK`) fails, and emits a Lean theorem pinning that down, so a
control that is meant to break one conjunct cannot silently break another.

Negative controls, per record:
  mutation_offset0   the bundle's own mutation (decode.py): offset[0] + 1   -> A d = c
  linear_entry       W[j][0] + 1 for a j with some A[i][j] != 0           -> A W = B
  offset_long        offset with an extra trailing 0                      -> shape only
  linear_row_long    W[0] with an extra trailing 0                        -> shape only
  linear_extra_row   W with an extra zero row                             -> shape only
  c_extra            c with an extra entry                                -> shape and rows
  half_offset        offset[0] + 1/2 (Python only: not an Int, so not
                     representable in Lean; see `integrality_*` instead)
Plus one fixed integrality instance, A = [[2]], B = [[2]], c = [1]: the prototype
accepts the rational witness W = [[1]], d = [1/2] with require_integral=False and
rejects it with True; Lean proves that NO integer certificate passes.
"""
from __future__ import annotations

import argparse
import copy
import json
import re
import sys
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "prototype"))

from forge.io.decode import verify, mutations, rational  # noqa: E402
from forge.witness.affine import AffineWitness, check_affine_witness  # noqa: E402

FAMILY = "Integral affine witness"


# --------------------------------------------------------------------------
# Integer mirror of lean/Forge/Checker/Affine.lean.
# --------------------------------------------------------------------------
def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def vadd(u, v):
    return [x + y for x, y in zip(u, v)]


def comb(p, a, W):
    out = [0] * p
    for aj, wj in reversed(list(zip(a, W))):
        out = vadd([aj * z for z in wj], out)
    return out


def shape_ok(A, B, c, W, d) -> bool:
    k = len(A[0]) if A else 0
    p = len(B[0]) if B else 0
    return (len(A) != 0 and len(A) == len(B) and len(A) == len(c) and k != 0 and p != 0
            and all(len(r) == k for r in A) and all(len(r) == p for r in B)
            and len(W) == k and len(d) == k and all(len(r) == p for r in W))


def rows_ok(p, W, d, A, B, c) -> bool:
    if not (len(A) == len(B) == len(c)):
        return False
    return all(dot(a, d) == ci and comb(p, a, W) == b for a, b, ci in zip(A, B, c))


def lean_check(A, B, c, W, d) -> tuple[bool, bool]:
    p = len(B[0]) if B else 0
    return shape_ok(A, B, c, W, d), rows_ok(p, W, d, A, B, c)


def python_check(A, B, c, W, d) -> bool:
    cert = AffineWitness(tuple(tuple(Q(v) for v in r) for r in W), tuple(Q(v) for v in d))
    return check_affine_witness(A, B, c, cert, True)


# --------------------------------------------------------------------------
# Decoding.
# --------------------------------------------------------------------------
def int_matrix(x, what):
    if not isinstance(x, list) or not all(isinstance(r, list) for r in x):
        raise SystemExit("%s: not a matrix" % what)
    return [int_vector(r, what) for r in x]


def int_vector(x, what):
    if not isinstance(x, list) or any(type(v) is not int for v in x):
        raise SystemExit("%s: entries must be JSON integers" % what)
    return list(x)


def integral(s: str, what) -> int:
    q = rational(s)
    if q.denominator != 1:
        raise SystemExit("%s: non-integral entry %s in an accepted certificate" % (what, s))
    return q.numerator


def decode(record):
    inp, cert = record["input"], record["certificate"]
    A = int_matrix(inp["A"], "A")
    B = int_matrix(inp["B"], "B")
    c = int_vector(inp["c"], "c")
    W = [[integral(v, "linear") for v in r] for r in cert["linear"]]
    d = [integral(v, "offset") for v in cert["offset"]]
    return A, B, c, W, d


# --------------------------------------------------------------------------
# Lean emission.
# --------------------------------------------------------------------------
def li(n: int) -> str:
    return "(%d)" % n if n < 0 else "%d" % n


def lvec(v) -> str:
    return "[" + ", ".join(li(x) for x in v) + "]"


def lmat(M) -> str:
    return "[" + ", ".join(lvec(r) for r in M) + "]"


def rsum(terms) -> str:
    """Right-nested sum, the shape `dot` unfolds to once `+ 0` is dropped."""
    if len(terms) == 1:
        return terms[0]
    return "%s + (%s)" % (terms[0], rsum(terms[1:]))


def lean_ident(s: str) -> str:
    s = re.sub(r"[^A-Za-z0-9_]", "_", s)
    return s if s[0].isalpha() else "c_" + s


def plus(expr: str, const: int) -> str:
    """`expr + const`, or `expr` alone when const is 0: `Int.add_zero` in the
    bridge's simp set erases a literal `+ 0`, so the statement must not carry one."""
    return expr if const == 0 else "%s + %s" % (expr, li(const))


def concrete(A, B, c, W, d):
    p = len(B[0])
    xs = ["x%d" % t for t in range(p)]
    ws = ["(%s)" % plus(rsum(["%s * %s" % (li(W[j][t]), xs[t]) for t in range(p)]), d[j])
          for j in range(len(W))]
    rows = []
    for a, b, ci in zip(A, B, c):
        lhs = rsum(["%s * %s" % (li(a[j]), ws[j]) for j in range(len(a))])
        rhs = plus("(%s)" % rsum(["%s * %s" % (li(b[t]), xs[t]) for t in range(p)]), ci)
        rows.append("%s = %s" % (lhs, rhs))
    wvars = ["w%d" % j for j in range(len(W))]
    ex_rows = []
    for a, b, ci in zip(A, B, c):
        lhs = rsum(["%s * %s" % (li(a[j]), wvars[j]) for j in range(len(a))])
        rhs = plus("(%s)" % rsum(["%s * %s" % (li(b[t]), xs[t]) for t in range(p)]), ci)
        ex_rows.append("%s = %s" % (lhs, rhs))
    return xs, ws, wvars, rows, ex_rows


HEADER = '''import Forge.Checker.Affine
/-
  GENERATED by tools/export_lean_affine.py from the prototype's certificate
  bundle (family "Integral affine witness"). Do not edit by hand; regenerate.

  Each certificate below was accepted by the prototype's
  `check_affine_witness(A, B, c, W, require_integral=True)` and by an integer
  re-implementation of `AffineCert.check` in the exporter, and is accepted here
  again by the Lean kernel via `decide`. No `native_decide`.

  The `_concrete` theorems are derived from `AffineCert.sound` by unfolding
  definitions with `simp only` and a single arithmetic lemma, `Int.add_zero`;
  no decision procedure proves them.

  Negative controls: the bundle's own mutation, plus controls that each break a
  named half of the checker. For the shape-only controls the file also proves
  that the row identities still hold, so the rejection is attributable to the
  shape test alone.
-/

namespace Forge.Checker.AffineCorpus
open Forge.Checker.Lin Forge.Checker.Affine
'''

FOOTER = '''
/-! ### Integrality

`A = [[2]]`, `B = [[2]]`, `c = [1]`. Over the rationals `W = [[1]]`, `d = [1/2]`
is a witness, and the prototype accepts it when `require_integral` is False and
rejects it when True (the exporter checks both). Here that rejection is a
theorem about ALL certificates: none passes, because `2 * w = 2 * x + 1` has no
integer solution at `x = 0`.
-/

def integrality_A : List (List Int) := [[2]]
def integrality_B : List (List Int) := [[2]]
def integrality_c : List Int := [1]

theorem integrality_no_certificate (w : AffineCert) :
    w.check integrality_A integrality_B integrality_c = false := by
  cases h : w.check integrality_A integrality_B integrality_c with
  | false => rfl
  | true =>
    have hs := AffineCert.sound _ _ _ w h []
    simp only [integrality_A, integrality_B, integrality_c, AffineCert.apply,
      mulVec_cons, mulVec_nil, dot_nil_right, vadd_cons_cons, vadd_nil_left] at hs
    revert hs
    generalize vadd (mulVec w.linear []) w.offset = v
    cases v with
    | nil => intro hs; exact absurd (List.cons.inj hs).1 (by decide)
    | cons v vs =>
      intro hs
      have h1 := (List.cons.inj hs).1
      simp only [dot_cons_cons, dot_nil_left, Int.add_zero] at h1
      omega

'''


def emit_positive(rid, A, B, c, W, d):
    n = lean_ident(rid)
    xs, ws, wvars, rows, ex_rows = concrete(A, B, c, W, d)
    L = []
    L.append("/-! ### `%s` --- %d equations, %d witness coordinates, %d parameters -/" %
             (rid, len(A), len(W), len(B[0])))
    L.append("")
    L.append("def %s_A : List (List Int) := %s" % (n, lmat(A)))
    L.append("def %s_B : List (List Int) := %s" % (n, lmat(B)))
    L.append("def %s_c : List Int := %s" % (n, lvec(c)))
    L.append("def %s_cert : AffineCert := { linear := %s, offset := %s }" % (n, lmat(W), lvec(d)))
    L.append("")
    L.append("/-- The checker accepts, by kernel reduction. -/")
    L.append("theorem %s_checks : %s_cert.check %s_A %s_B %s_c = true := by decide" % (n, n, n, n, n))
    L.append("")
    L.append("/-- For every `x`, `w = W x + d` solves `A w = B x + c`. -/")
    L.append("theorem %s_sound (x : List Int) :" % n)
    L.append("    mulVec %s_A (%s_cert.apply x) = vadd (mulVec %s_B x) %s_c :=" % (n, n, n, n))
    L.append("  AffineCert.sound _ _ _ _ %s_checks x" % n)
    L.append("")
    binders = " ".join(xs)
    L.append("/-- The same fact in ordinary arithmetic, with the witness substituted. -/")
    L.append("theorem %s_concrete (%s : Int) :" % (n, binders))
    L.append("    " + " ∧\n    ".join(rows) + " := by")
    L.append("  have h := %s_sound [%s]" % (n, ", ".join(xs)))
    L.append("  simp only [%s_A, %s_B, %s_c, %s_cert, AffineCert.apply, mulVec_cons, mulVec_nil," % (n, n, n, n))
    L.append("    dot_cons_cons, dot_nil_right, vadd_cons_cons, vadd_nil_left,")
    L.append("    Int.add_zero, List.cons.injEq] at h")
    hyps = ["h%d" % i for i in range(len(A))]
    L.append("  obtain ⟨%s, -⟩ := h" % ", ".join(hyps))
    L.append("  exact ⟨%s⟩" % ", ".join(hyps) if len(hyps) > 1 else "  exact h0")
    L.append("")
    L.append("/-- Integral Skolem form: for all parameters there is an integer solution. -/")
    L.append("theorem %s_exists (%s : Int) :" % (n, binders))
    L.append("    ∃ %s : Int, %s :=" % (" ".join(wvars), " ∧ ".join(ex_rows)))
    L.append("  ⟨%s, %s_concrete %s⟩" % (", ".join(ws), n, binders))
    L.append("")
    return L


def emit_negative(rid, tag, why, A, B, c, W, d, shape, rows):
    n = "%s_%s" % (lean_ident(rid), tag)
    L = []
    L.append("/-- NEGATIVE CONTROL `%s`: %s" % (tag, why))
    L.append("shapeOK = %s, rowsOK = %s (checked in Python and below). -/" % (
        "true" if shape else "false", "true" if rows else "false"))
    L.append("def %s_A : List (List Int) := %s" % (n, lmat(A)))
    L.append("def %s_B : List (List Int) := %s" % (n, lmat(B)))
    L.append("def %s_c : List Int := %s" % (n, lvec(c)))
    L.append("def %s_cert : AffineCert := { linear := %s, offset := %s }" % (n, lmat(W), lvec(d)))
    L.append("theorem %s_rejected : %s_cert.check %s_A %s_B %s_c = false := by decide" % (n, n, n, n, n))
    L.append("theorem %s_halves :" % n)
    L.append("    shapeOK %s_A %s_B %s_c %s_cert = %s ∧" % (n, n, n, n, "true" if shape else "false"))
    L.append("    rowsOK (%s_B.headD []).length %s_cert.linear %s_cert.offset %s_A %s_B %s_c = %s := by decide"
             % (n, n, n, n, n, n, "true" if rows else "false"))
    L.append("#guard %s_cert.check %s_A %s_B %s_c = false" % (n, n, n, n))
    L.append("")
    return L


def negatives(record, A, B, c, W, d):
    """Yield (tag, why, A, B, c, W, d, expected_shape, expected_rows)."""
    out = []
    muts = mutations(record)
    if len(muts) != 1:
        raise SystemExit("expected exactly one bundle mutation, got %d" % len(muts))
    if verify(muts[0]):
        raise SystemExit("bundle mutation accepted by the prototype")
    mA, mB, mc, mW, md = decode(muts[0])
    out.append(("mutation_offset0", "the bundle's own mutation, `offset[0] + 1`; breaks `A d = c`.",
                mA, mB, mc, mW, md, True, False))
    j = next((j for j in range(len(A[0])) if any(a[j] != 0 for a in A)), None)
    if j is None:
        raise SystemExit("A is zero; no linear-entry control possible")
    W2 = copy.deepcopy(W); W2[j][0] += 1
    out.append(("linear_entry", "`W[%d][0] + 1`, a column of `A` that is not zero; breaks `A W = B`." % j,
                A, B, c, W2, d, True, False))
    out.append(("offset_long", "`offset` with an extra trailing 0; the truncating row identities still hold.",
                A, B, c, W, d + [0], False, True))
    W3 = copy.deepcopy(W); W3[0] = W3[0] + [0]
    out.append(("linear_row_long", "`W[0]` with an extra trailing 0; only the row-width test fails.",
                A, B, c, W3, d, False, True))
    W4 = copy.deepcopy(W) + [[0] * len(B[0])]
    out.append(("linear_extra_row", "`W` with an extra zero row; only the row-count test fails.",
                A, B, c, W4, d, False, True))
    out.append(("c_extra", "`c` with an extra entry; the rows of `A`, `B`, `c` no longer run out together.",
                A, B, c + [0], W, d, False, False))
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--bundle", type=Path,
                    default=ROOT / "prototype" / "results" / "certificates.json")
    ap.add_argument("--out", type=Path,
                    default=ROOT / "lean" / "Forge" / "Checker" / "AffineCorpus.lean")
    ap.add_argument("--json", type=Path,
                    default=ROOT / "results" / "lean-affine-corpus.json")
    args = ap.parse_args()

    records = json.loads(args.bundle.read_text(encoding="utf-8"))
    wanted = [r for r in records if r["family"] == FAMILY]
    if not wanted:
        raise SystemExit("no integral affine witnesses in the bundle")

    body, summary = [], []
    for rec in wanted:
        if not verify(rec):
            raise SystemExit("%s: prototype rejects its own bundle record" % rec["id"])
        A, B, c, W, d = decode(rec)
        if not python_check(A, B, c, W, d) or lean_check(A, B, c, W, d) != (True, True):
            raise SystemExit("%s: integer re-check disagrees with the prototype" % rec["id"])
        body += emit_positive(rec["id"], A, B, c, W, d)
        controls = []
        for tag, why, nA, nB, nc, nW, nd, es, er in negatives(rec, A, B, c, W, d):
            py = python_check(nA, nB, nc, nW, nd)
            s, r = lean_check(nA, nB, nc, nW, nd)
            if py or (s, r) != (es, er):
                raise SystemExit("%s/%s: control not as designed (python=%s shape=%s rows=%s)"
                                 % (rec["id"], tag, py, s, r))
            body += emit_negative(rec["id"], tag, why, nA, nB, nc, nW, nd, s, r)
            controls.append({"control": tag, "prototype_accepts": py, "shapeOK": s, "rowsOK": r})
        # Integrality control on the record itself: Python only (not an Int).
        half = [str(Q(d[0]) + Q(1, 2))] + [str(v) for v in d[1:]]
        hcert = AffineWitness(tuple(tuple(Q(v) for v in r) for r in W), tuple(Q(v) for v in half))
        if check_affine_witness(A, B, c, hcert, True):
            raise SystemExit("%s: half-integral offset accepted" % rec["id"])
        controls.append({"control": "half_offset", "prototype_accepts": False,
                         "lean": "not representable: entries are Int"})
        summary.append({"id": rec["id"], "equations": len(A), "witness_coordinates": len(W),
                        "parameters": len(B[0]), "negative_controls": controls})

    # Fixed integrality instance.
    rat = AffineWitness(((Q(1),),), (Q(1, 2),))
    if not check_affine_witness([[2]], [[2]], [1], rat, False):
        raise SystemExit("integrality instance: rational witness not accepted without integrality")
    if check_affine_witness([[2]], [[2]], [1], rat, True):
        raise SystemExit("integrality instance: rational witness accepted with integrality")

    text = HEADER + "\n" + "\n".join(body) + FOOTER
    names = []
    for rec in wanted:
        n = lean_ident(rec["id"])
        names += ["%s_checks" % n, "%s_sound" % n, "%s_concrete" % n, "%s_exists" % n]
        names += ["%s_%s_rejected" % (n, t["control"]) for t in
                  next(s for s in summary if s["id"] == rec["id"])["negative_controls"]
                  if "shapeOK" in t]
    names.append("integrality_no_certificate")
    text += "".join("#print axioms %s\n" % x for x in names)
    text += "\nend Forge.Checker.AffineCorpus\n"
    args.out.write_text(text, encoding="utf-8")

    args.json.write_text(json.dumps({
        "what": ("Every integral affine witness in the prototype bundle, emitted as Int "
                 "data for Forge.Checker.Affine, with negative controls. Each verdict is "
                 "checked by the prototype's check_affine_witness(require_integral=True) "
                 "and by an integer mirror of AffineCert.check before emission, and again "
                 "by the Lean kernel when AffineCorpus.lean is elaborated."),
        "generated_lean": "lean/Forge/Checker/AffineCorpus.lean",
        "checked_by": "kernel reduction via `decide`; native_decide is not used",
        "certificates": summary,
    }, indent=2) + "\n", encoding="utf-8")
    print("wrote %s" % args.out)
    for s in summary:
        print("  %-20s m=%d k=%d p=%d controls=%d" % (s["id"], s["equations"],
              s["witness_coordinates"], s["parameters"], len(s["negative_controls"])))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
