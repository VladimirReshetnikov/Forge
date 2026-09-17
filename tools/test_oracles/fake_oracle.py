#!/usr/bin/env python3
"""Adversarial stand-ins for tools/forge_oracle.py, for OracleTest.lean.

Usage:  python tools/test_oracles/fake_oracle.py MODE

Every mode reads the problem on stdin exactly like the real oracle. Most modes
first run the REAL search (forge_oracle.solve_problem) and then corrupt its
answer, so each corruption is a small, targeted mutation of a certificate that
would otherwise have been accepted. The `identity` mode passes the real answer
through unchanged and is the positive control for the harness itself.

None of these is used by anything except the negative tests. They exist to show
that the Lean side rejects bad data at the boundary and never admits.
"""
from __future__ import annotations

import copy
import json
import os
import sys
import time
from pathlib import Path

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))

import forge_oracle as oracle  # noqa: E402


def real(raw: bytes) -> dict:
    out, _code = oracle.solve_raw(raw)
    if out.get("status") != "certificate":
        # A fake oracle must corrupt a real certificate; if there is none the
        # test setup is wrong, and saying so is better than emitting garbage.
        sys.stderr.write("fake_oracle: real oracle found no certificate: %r\n" % out)
        sys.exit(3)
    return out


def dumps(obj) -> str:
    return json.dumps(obj, separators=(",", ":"))


def first_nonzero_square(cert):
    for s in cert["squares"]:
        if s["weight"] != 0:
            return s
    raise SystemExit("no nonzero weight")


def mutate(mode: str, raw: bytes) -> tuple[str, int]:
    """Return (stdout text, exit code)."""
    # --- modes that need no real certificate -------------------------------
    if mode == "garbage":
        return "hello, I am not JSON\n", 0
    if mode == "empty":
        return "", 0
    if mode == "unknown":
        return dumps({"status": "unknown", "reason": "fake oracle declines"}), 0
    if mode == "badstatus":
        return dumps({"status": "proved", "reason": "trust me"}), 0
    if mode == "sleep":
        time.sleep(30)
        return "", 0
    if mode == "flood":
        # Never terminates on its own: an unbounded reply.
        chunk = " " * 65536
        while True:
            sys.stdout.write(chunk)
            sys.stdout.flush()
    if mode == "exponent":
        return ('{"status":"certificate","scale":1e999999999,"squares":[],'
                '"multipliers":[]}'), 0

    cert = real(raw)
    text = None
    code = 0

    if mode == "identity":
        pass
    elif mode == "oversize_valid":                # a VALID certificate past checkSize
        # Zero-weight squares change nothing about the identity, so a checker with
        # no size limit would accept this; each 45-term square adds 2025 to the
        # expanded size. The decoder must refuse it BEFORE checking, and say that
        # the refusal is a resource limit, not a verdict.
        n = json.loads(raw)["target"]["n"]
        big = {"n": n, "terms": [[[j] + [0] * (n - 1), 1] for j in range(45)]}
        cert["squares"].append({"weight": 0, "powers": [0] * len(cert["squares"][0]["powers"]),
                                "poly": big})
    elif mode == "negweight":                     # (a)
        s = first_nonzero_square(cert)
        s["weight"] = -s["weight"]
    elif mode == "wrongmult":                     # (b)
        m = cert["multipliers"][0]
        m["terms"][0][1] += 1
    elif mode == "truncated":                     # (c)
        full = dumps(cert)
        text = full[: len(full) // 2]
    elif mode == "float":                         # (d) 1.5
        cert["squares"][0]["poly"]["terms"][0][1] = 1.5
    elif mode == "float_integral":                # (d) 7.0 -- integral value, float syntax
        cert["scale"] = float(cert["scale"])
    elif mode == "string_coeff":                  # (d) "7" -- the INPUT convention, not the output one
        t = cert["squares"][0]["poly"]["terms"][0]
        t[1] = str(t[1])
    elif mode == "otherproblem":                  # (e) a certificate for target + 1
        prob = json.loads(raw)
        n = prob["target"]["n"]
        terms = prob["target"]["terms"]
        for t in terms:
            if all(e == 0 for e in t[0]):
                t[1] = str(int(t[1]) + 1)
                break
        else:
            terms.append([[0] * n, "1"])
        cert = real(json.dumps(prob).encode())
    elif mode == "extrafield":                    # (f)
        cert["comment"] = "an extra top-level field"
    elif mode == "extrasquarefield":              # (f)
        cert["squares"][0]["note"] = "an extra field in a square"
    elif mode == "missingfield":                  # (f)
        del cert["multipliers"]
    elif mode == "missingpolyn":                  # (f)
        del cert["squares"][0]["poly"]["n"]
    elif mode == "dupkey":                        # (f) duplicate key; the later value is valid
        full = dumps(cert)
        text = '{"scale":999,' + full[1:]
    elif mode == "nullfield":                     # (f) right field, wrong type
        cert["multipliers"] = None
    elif mode == "bigint":                        # (g) 10^200, beyond the digit bound
        cert["scale"] = 10 ** 200
    elif mode == "bigint_inbounds":               # (g) 10^99: decodes, then fails the check
        cert["scale"] = 10 ** 99
    elif mode == "oversized":                     # (g) valid JSON padded past 1 MB
        text = dumps(cert) + " " * 1_100_000
    elif mode == "wrongn":
        for s in cert["squares"]:
            s["poly"]["n"] += 1
            for t in s["poly"]["terms"]:
                t[0].append(0)
    elif mode == "powerslen":
        for s in cert["squares"]:
            s["powers"].append(0)
    elif mode == "negpower":
        cert["squares"][0]["powers"][0] = -1
    elif mode == "extramult":
        cert["multipliers"].append({"n": cert["squares"][0]["poly"]["n"], "terms": []})
    elif mode == "scale0":
        cert["scale"] = 0
    elif mode == "bool":
        cert["squares"][0]["weight"] = True
    elif mode == "two":
        text = dumps(cert) + "\n" + dumps(cert)
    elif mode == "exit1":
        code = 1
    elif mode == "dropsquare":
        cert["squares"] = cert["squares"][1:]
    else:
        sys.stderr.write("fake_oracle: unknown mode %r\n" % mode)
        return "", 4
    if text is None:
        text = dumps(cert)
    return text, code


def main() -> None:
    if len(sys.argv) != 2:
        sys.stderr.write("usage: fake_oracle.py MODE\n")
        os._exit(4)
    raw = sys.stdin.buffer.read(oracle.MAX_INPUT_BYTES + 1)
    text, code = mutate(sys.argv[1], raw)
    sys.stdout.write(text)
    sys.stdout.flush()
    os._exit(code)


if __name__ == "__main__":
    main()
