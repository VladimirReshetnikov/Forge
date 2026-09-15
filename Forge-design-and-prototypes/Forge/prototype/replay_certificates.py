#!/usr/bin/env python3
"""Replay all stored certificates, using Python's standard library only.

Usage: python -S replay_certificates.py ../results/certificates
The -S check is intentional: SciPy is required for discovery, not verification.
The JSON fixtures include problem statements; production integration must bind
those statements to the original Lean goal, not let an oracle replace them.
"""
from fractions import Fraction as Q
import argparse
import json
from pathlib import Path
from forge_proto.poly import Poly
from forge_proto.recurrence import check_recurrence
from forge_proto.positivity import WeightedSquare, SOSCertificate, check_sos, check_bernstein
from forge_proto.witness import Affine, WitnessProblem, WitnessCertificate, check_witness
from forge_proto.induction import Term, Equation, RewriteStep, EqualityTrace, InductionCertificate, Theory


def term(v):
    return Term(v["op"], tuple(term(a) for a in v["args"]), v["name"], v["sort"])


def trace(v):
    return EqualityTrace(*(tuple(RewriteStep(s["rule"], tuple(s["path"])) for s in v[side])
                           for side in ("left", "right")))


def affine(v):
    return Affine.make(v["coefficients"], v["constant"])


def replay(directory: Path):
    counts = {}
    def read(name): return json.loads((directory / (name + ".json")).read_text())
    theory = Theory()
    counts["induction"] = 0
    for row in read("induction"):
        c = row["certificate"]
        cert = InductionCertificate(Equation(term(c["equation"]["left"]), term(c["equation"]["right"])),
                                    c["variable"], trace(c["base"]), trace(c["step"]))
        if not theory.install(row["name"], cert):
            raise ValueError("rejected induction certificate: " + row["name"])
        counts["induction"] += 1
    for name in ("recurrences", "witnesses", "sos", "bernstein"):
        counts[name] = 0
        for row in read(name):
            if name == "recurrences":
                ok = check_recurrence(Poly.from_json(row["increment"]), Q(row["initial"]), Poly.from_json(row["candidate"]))
            elif name == "witnesses":
                problem = WitnessProblem(row["inputs"], row["outputs"], tuple(map(affine, row["domain"])), tuple(map(affine, row["goals"])))
                c = row["certificate"]
                cert = WitnessCertificate(tuple(map(affine, c["witnesses"])), tuple(tuple(map(Q, r)) for r in c["multipliers"]), tuple(map(Q, c["slacks"])))
                ok = check_witness(problem, cert)
            elif name == "sos":
                cert = SOSCertificate(tuple(WeightedSquare(Q(s["weight"]), Poly.from_json(s["root"]), s["constraint"])
                                            for s in row["certificate"]["squares"]))
                ok = check_sos(Poly.from_json(row["target"]), list(map(Poly.from_json, row["constraints"])), cert)
            else:
                ok = check_bernstein(Poly.from_json(row["target"]), row["box"], row["tree"], strict=row["strict"])
            if not ok:
                raise ValueError(f"rejected {name} certificate: {row['name']}")
            counts[name] += 1
    counts["total"] = sum(counts.values())
    print(json.dumps(counts, indent=2))
    return counts


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("directory", nargs="?", type=Path, default=Path(__file__).resolve().parent.parent / "results" / "certificates")
    replay(p.parse_args().directory)
