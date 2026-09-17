#!/usr/bin/env python3
"""The producer side of the `forge_cone?` oracle protocol.

Reads ONE JSON problem on stdin and prints ONE JSON object on stdout.

INPUT (the polynomial shape of tools/export_lean_cone.py):

    {"target":       {"n": k, "terms": [[[e0, ..., e(k-1)], "c"], ...]},
     "inequalities": [Poly, ...],
     "equalities":   [Poly, ...]}

Exactly these three keys; every Poly exactly {"n", "terms"}; every `n` equal;
every monomial of length exactly `n` with nonnegative integer exponents; every
coefficient an INTEGER, given as a decimal string or a JSON integer (the Lean
side sends strings). Duplicate object keys, duplicate monomials, floats, NaN
and Infinity are rejected.

MEANING. Find a certificate that `target >= 0` wherever every inequality is
`>= 0` and every equality is `= 0`.

OUTPUT, exactly one of

    {"status": "certificate", "scale": D,
     "squares": [{"weight": w, "powers": [e_1, ..., e_m], "poly": Poly}, ...],
     "multipliers": [Poly, ...]}
    {"status": "unknown", "reason": "..."}
    {"status": "error",   "reason": "..."}        (input rejected; exit code 2)

In a certificate every number is a JSON INTEGER (coefficients too, unlike the
input), `n` is the input's `n`, and the integer identity

    D * target = sum_i w_i * prod_k g_k^e_ik * q_i^2 + sum_j h_j * f_j

has been re-checked in Python by tools/export_lean_cone.py's `convert`, which
is imported and reused here rather than reimplemented. The Lean side trusts
none of this: it decodes strictly and the kernel re-checks the identity.

SEARCH. The prototype's own procedures, nothing new:
  * `prototype/forge/quadratic.py::quadratic_sos` for unconstrained targets of
    degree <= 2 (exact Schur complement, no floating point);
  * `prototype/forge/cone.py::discover` (finite dictionary cone + LP + exact
    rational repair) at search degree max(2, even ceiling of the input degree),
    then +2, capped at SEARCH_DEGREE_CAP.
Neither is complete. "unknown" is never a disproof.

BOUNDS (input is rejected with status "error" beyond these):
  MAX_INPUT_BYTES   1_000_000 bytes of stdin
  MAX_VARIABLES     6         (n)
  MAX_DEGREE        4         total degree of target and of every constraint
  MAX_TERMS         200       terms per polynomial
  MAX_CONSTRAINTS   8         inequalities, and separately equalities
  MAX_COEFF_DIGITS  60        decimal digits per input coefficient
and a certificate is replaced by "unknown" if it exceeds the OUTPUT bounds the
Lean decoder enforces (MAX_OUT_* below), or if its estimated checkable size
exceeds MAX_CHECK_SIZE.

An earlier version said this meant "a well-behaved oracle never emits something
the consumer is bound to reject for size". That was false: review showed the
Lean checker could not check certificates far inside MAX_OUT_SQUARES and
MAX_OUT_TERMS, because the kernel's limit tracks the EXPANDED identity, not the
counts. MAX_CHECK_SIZE mirrors Lean's measured limit. The estimate here uses the
COLLECTED polynomials this process is sent, which can be shorter than the
unnormalised lists Lean multiplies, so it is a lower bound: the Lean decoder's
`checkSize` is authoritative and may still refuse.

TIME. `--timeout SECONDS` (default 20) is enforced on the whole search by a
watchdog: the search runs in a daemon thread, and if it has not finished the
process prints "unknown" and exits with `os._exit`. The LP backend is also
handed the remaining time.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import threading
import time
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / "tools"
PROTOTYPE = ROOT / "prototype"
for p in (str(TOOLS), str(PROTOTYPE)):
    if p not in sys.path:
        sys.path.insert(0, p)

MAX_INPUT_BYTES = 1_000_000
MAX_VARIABLES = 6
MAX_DEGREE = 4
MAX_TERMS = 200
MAX_CONSTRAINTS = 8
MAX_COEFF_DIGITS = 60
SEARCH_DEGREE_CAP = 4
DEFAULT_TIMEOUT = 20.0

# Output bounds: must not exceed the Lean decoder's (Oracle.lean).
MAX_CHECK_SIZE = 1600      # mirrors Forge.Checker.Oracle.measuredCheckLimit
MAX_OUT_SQUARES = 1000
MAX_OUT_TERMS = 1000
MAX_OUT_DIGITS = 100
MAX_OUT_EXPONENT = 64
MAX_OUT_BYTES = 1_000_000

INPUT_KEYS = {"target", "inequalities", "equalities"}
POLY_KEYS = {"n", "terms"}


class InputError(ValueError):
    pass


# --------------------------------------------------------------------------
# Strict input parsing.
# --------------------------------------------------------------------------
def _no_duplicates(pairs):
    out = {}
    for k, v in pairs:
        if k in out:
            raise InputError("duplicate key %r" % k)
        out[k] = v
    return out


def _reject_float(s):
    raise InputError("non-integer number %s" % s)


def _reject_constant(s):
    raise InputError("non-finite number %s" % s)


def _int_coeff(c) -> int:
    if isinstance(c, bool):
        raise InputError("boolean coefficient")
    if isinstance(c, int):
        v = c
    elif isinstance(c, str):
        body = c[1:] if c.startswith("-") else c
        if not body or not body.isascii() or not body.isdigit():
            raise InputError("coefficient %r is not a decimal integer" % c)
        v = int(c)
    else:
        raise InputError("coefficient %r is not an integer" % (c,))
    if len(str(abs(v))) > MAX_COEFF_DIGITS:
        raise InputError("coefficient has more than %d digits" % MAX_COEFF_DIGITS)
    return v


def _poly(obj, n_expected=None):
    if not isinstance(obj, dict) or set(obj) != POLY_KEYS:
        raise InputError("a polynomial must be an object with exactly the keys n, terms")
    n = obj["n"]
    if isinstance(n, bool) or not isinstance(n, int) or n < 0:
        raise InputError("n must be a nonnegative integer")
    if n > MAX_VARIABLES:
        raise InputError("more than %d variables (n = %d)" % (MAX_VARIABLES, n))
    if n_expected is not None and n != n_expected:
        raise InputError("polynomials disagree on n (%d vs %d)" % (n, n_expected))
    terms = obj["terms"]
    if not isinstance(terms, list):
        raise InputError("terms must be a list")
    if len(terms) > MAX_TERMS:
        raise InputError("more than %d terms in a polynomial" % MAX_TERMS)
    seen = {}
    for t in terms:
        if not isinstance(t, list) or len(t) != 2:
            raise InputError("a term must be a pair [monomial, coefficient]")
        mono, c = t
        if not isinstance(mono, list) or len(mono) != n:
            raise InputError("a monomial must be a list of exactly n exponents")
        for e in mono:
            if isinstance(e, bool) or not isinstance(e, int) or e < 0:
                raise InputError("exponents must be nonnegative integers")
        if sum(mono) > MAX_DEGREE:
            raise InputError("degree exceeds %d" % MAX_DEGREE)
        key = tuple(mono)
        if key in seen:
            raise InputError("duplicate monomial %r" % (mono,))
        seen[key] = _int_coeff(c)
    return n, [(m, c) for m, c in seen.items()]


def parse_problem(raw: bytes):
    if len(raw) > MAX_INPUT_BYTES:
        raise InputError("input exceeds %d bytes" % MAX_INPUT_BYTES)
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError:
        raise InputError("input is not UTF-8")
    try:
        obj = json.loads(text, object_pairs_hook=_no_duplicates,
                         parse_float=_reject_float, parse_constant=_reject_constant)
    except InputError:
        raise
    except ValueError as e:
        raise InputError("input is not valid JSON: %s" % e)
    if not isinstance(obj, dict) or set(obj) != INPUT_KEYS:
        raise InputError("input must be an object with exactly the keys "
                         "target, inequalities, equalities")
    n, target = _poly(obj["target"])
    ineqs, eqs = obj["inequalities"], obj["equalities"]
    if not isinstance(ineqs, list) or not isinstance(eqs, list):
        raise InputError("inequalities and equalities must be lists")
    if len(ineqs) > MAX_CONSTRAINTS or len(eqs) > MAX_CONSTRAINTS:
        raise InputError("more than %d constraints of one kind" % MAX_CONSTRAINTS)
    ineqs = [_poly(g, n)[1] for g in ineqs]
    eqs = [_poly(f, n)[1] for f in eqs]
    return n, target, ineqs, eqs


# --------------------------------------------------------------------------
# Search, through the prototype.
# --------------------------------------------------------------------------
def _proto_poly(width, terms):
    """The prototype's Poly needs n >= 1: a 0-variable problem gets one unused
    padding variable, stripped again on output."""
    from forge.poly import Poly
    pad = width - (len(terms[0][0]) if terms else width)
    return Poly.make(width, [(tuple(m) + (0,) * pad, c) for m, c in terms])


def _pad_all(n, width, terms):
    return [(tuple(m) + (0,) * (width - n), c) for m, c in terms]


def search(n, target, ineqs, eqs, deadline):
    """Return (ConeCertificate, width, prototype polys) or (None, reason)."""
    from forge.poly import Poly
    from forge.quadratic import quadratic_sos
    from forge import cone

    width = max(n, 1)
    P = Poly.make(width, _pad_all(n, width, target))
    Gs = [Poly.make(width, _pad_all(n, width, g)) for g in ineqs]
    Fs = [Poly.make(width, _pad_all(n, width, f)) for f in eqs]
    reasons = []

    if not Gs and not Fs and P.degree <= 2:
        try:
            cert = quadratic_sos(P)
        except AssertionError as e:  # the prototype's own self-check failed
            cert = None
            reasons.append("quadratic_sos self-check failed: %s" % e)
        if cert is not None:
            return (cert, width, P, Gs, Fs), None
        reasons.append("quadratic_sos: not PSD or outside fragment")

    deg = max([P.degree] + [g.degree for g in Gs] + [f.degree for f in Fs] + [0])
    d0 = max(2, deg + (deg % 2))
    for d in (d0, d0 + 2):
        if d > SEARCH_DEGREE_CAP:
            break
        remaining = deadline - time.monotonic()
        if remaining <= 0.5:
            reasons.append("time budget exhausted before degree %d" % d)
            break
        try:
            res = cone.discover(P, Gs, Fs, degree=d, timeout_seconds=remaining)
        except Exception as e:  # noqa: BLE001 -- any search failure is UNKNOWN
            reasons.append("cone.discover(degree=%d) raised %s: %s"
                           % (d, type(e).__name__, e))
            continue
        if res.status == "proved" and res.certificate is not None:
            return (res.certificate, width, P, Gs, Fs), None
        reasons.append("cone.discover(degree=%d): %s" % (d, res.reason))
    return None, "; ".join(reasons) or "no search applies"


# --------------------------------------------------------------------------
# Conversion, through tools/export_lean_cone.py.
# --------------------------------------------------------------------------
def _int_poly_json(n, terms):
    out = []
    for m, c in terms:
        m = list(m)
        if any(m[n:]):
            raise ValueError("padding variable used by the certificate")
        out.append([m[:n], int(c)])
    return {"n": n, "terms": out}


def _norm(terms):
    acc = {}
    for m, c in terms:
        acc[tuple(m)] = acc.get(tuple(m), 0) + c
    return {m: c for m, c in acc.items() if c != 0}


def to_integer_certificate(n, found):
    import export_lean_cone as exporter
    from forge.certificates import cone_json

    cert, width, P, Gs, Fs = found
    record = {
        "id": "oracle",
        "family": "oracle",
        "input": {"p": P.json(),
                  "inequalities": [g.json() for g in Gs],
                  "equalities": [f.json() for f in Fs]},
        "certificate": cone_json(cert),
    }
    conv = exporter.convert(record)  # re-checks the integer identity or raises
    # The input was integral, so the exporter must not have rescaled the problem:
    # a certificate for `d * target` would be a certificate for a different
    # problem as far as the consumer is concerned.
    if conv["p_multiplier"] != 1 or \
            _norm(conv["target"]) != _norm([(m, int(c)) for m, c in P.terms]):
        raise ValueError("exporter changed the target")
    for G, g in zip(conv["ineqs"], Gs):
        if _norm(G) != _norm([(m, int(c)) for m, c in g.terms]):
            raise ValueError("exporter changed an inequality")
    for F, f in zip(conv["eqs"], Fs):
        if _norm(F) != _norm([(m, int(c)) for m, c in f.terms]):
            raise ValueError("exporter changed an equality")
    return {
        "status": "certificate",
        "scale": int(conv["scale"]),
        "squares": [{"weight": int(s["weight"]),
                     "powers": [int(e) for e in s["powers"]],
                     "poly": _int_poly_json(n, s["poly"])}
                    for s in conv["squares"]],
        "multipliers": [_int_poly_json(n, h) for h in conv["multipliers"]],
    }


def within_output_bounds(out) -> str | None:
    def digits_ok(v):
        return len(str(abs(v))) <= MAX_OUT_DIGITS

    if len(out["squares"]) > MAX_OUT_SQUARES:
        return "too many squares"
    if not digits_ok(out["scale"]):
        return "scale too large"
    polys = [s["poly"] for s in out["squares"]] + out["multipliers"]
    for s in out["squares"]:
        if not digits_ok(s["weight"]) or any(e > MAX_OUT_EXPONENT for e in s["powers"]):
            return "weight or power too large"
    for p in polys:
        if len(p["terms"]) > MAX_OUT_TERMS:
            return "too many terms"
        for m, c in p["terms"]:
            if not digits_ok(c) or any(e > MAX_OUT_EXPONENT for e in m):
                return "coefficient or exponent too large"
    if len(dumps(out)) > MAX_OUT_BYTES:
        return "output too large"
    return None


def check_size(out, target, ineqs, eqs) -> int:
    """Mirror of Forge.Checker.Oracle.checkSize: the length of the list the Lean
    checker's `collect` receives. Uses the collected polynomials this process was
    sent, so it can UNDER-estimate Lean's figure; Lean's check is authoritative."""
    def size(poly) -> int:
        return len(poly)        # parse_problem yields lists of (monomial, coeff)

    total = size(target)
    for sq in out["squares"]:
        product = 1
        for e, g in zip(sq["powers"], ineqs):
            product *= size(g) ** e
        q = len(sq["poly"]["terms"])
        total += product * q * q
    for h, f in zip(out["multipliers"], eqs):
        total += len(h["terms"]) * size(f)
    return total


def dumps(obj) -> str:
    return json.dumps(obj, separators=(",", ":"))


# --------------------------------------------------------------------------
# Entry points.
# --------------------------------------------------------------------------
def solve_problem(n, target, ineqs, eqs, timeout=DEFAULT_TIMEOUT) -> dict:
    """Search and convert. Importable by the fake oracles in tools/test_oracles."""
    deadline = time.monotonic() + timeout
    found, reason = search(n, target, ineqs, eqs, deadline)
    if found is None:
        return {"status": "unknown", "reason": reason}
    try:
        out = to_integer_certificate(n, found)
    except Exception as e:  # noqa: BLE001 -- a conversion defect is never a guess
        return {"status": "unknown",
                "reason": "integer conversion failed: %s: %s" % (type(e).__name__, e)}
    bad = within_output_bounds(out)
    if bad is not None:
        return {"status": "unknown", "reason": "certificate exceeds output bounds: " + bad}
    size = check_size(out, target, ineqs, eqs)
    if size > MAX_CHECK_SIZE:
        return {"status": "unknown",
                "reason": "certificate found, but its expanded identity (%d terms) exceeds "
                          "the %d that Lean's kernel check was measured to handle" %
                          (size, MAX_CHECK_SIZE)}
    return out


def solve_raw(raw: bytes, timeout=DEFAULT_TIMEOUT) -> tuple[dict, int]:
    try:
        n, target, ineqs, eqs = parse_problem(raw)
    except InputError as e:
        return {"status": "error", "reason": str(e)}, 2
    return solve_problem(n, target, ineqs, eqs, timeout), 0


def read_stdin_bounded() -> bytes:
    return sys.stdin.buffer.read(MAX_INPUT_BYTES + 1)


def emit(obj: dict, code: int) -> None:
    sys.stdout.write(dumps(obj) + "\n")
    sys.stdout.flush()
    os._exit(code)


def main() -> None:
    ap = argparse.ArgumentParser(description="forge_cone? oracle")
    ap.add_argument("--timeout", type=float, default=DEFAULT_TIMEOUT,
                    help="wall-clock seconds for the whole search (default 20)")
    args = ap.parse_args()
    if not args.timeout > 0:
        emit({"status": "error", "reason": "timeout must be positive"}, 2)

    raw = read_stdin_bounded()
    result: dict = {}

    def work():
        try:
            result["value"] = solve_raw(raw, args.timeout)
        except Exception as e:  # noqa: BLE001
            result["value"] = ({"status": "unknown",
                                "reason": "internal error: %s: %s" % (type(e).__name__, e)}, 0)

    t = threading.Thread(target=work, daemon=True)
    t.start()
    t.join(args.timeout)
    if "value" not in result:
        emit({"status": "unknown", "reason": "timeout after %g s" % args.timeout}, 0)
    emit(*result["value"])


if __name__ == "__main__":
    main()
