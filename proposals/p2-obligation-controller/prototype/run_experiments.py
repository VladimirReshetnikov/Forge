#!/usr/bin/env python3
"""Reproduce designed micro-experiments. This is NOT a Lean/grind benchmark."""
from __future__ import annotations
import argparse
import json
import platform
import random
import sys
import time
from dataclasses import asdict
from fractions import Fraction as Q
from pathlib import Path

from forge_proto.poly import Poly
from forge_proto.recurrence import synthesize_recurrence, check_recurrence
from forge_proto.positivity import search_sos, check_sos, square_dictionary, search_bernstein, check_bernstein
from forge_proto.witness import Affine, WitnessProblem, synthesize_witness, check_witness
from forge_proto.induction import demonstration_theory, Equation, RA, R, V, N, discover_accumulator_lemma


def measured(f):
    start = time.perf_counter()
    value = f()
    return value, time.perf_counter() - start


def run(output: Path):
    import numpy, scipy
    output.mkdir(parents=True, exist_ok=True)
    certificates = output / "certificates"
    certificates.mkdir(exist_ok=True)
    results = {
        "description": "Designed Python micro-experiments, not a representative Lean benchmark",
        "baseline_lean_release_inspected": "v4.34.0 (2026-09-14)",
        "lean_executed": False,
        "environment": {"python": sys.version, "platform": platform.platform(),
                        "scipy": scipy.__version__, "numpy": numpy.__version__},
        "seeds": {"recurrences": 420, "witnesses": 421, "sos": 422, "bernstein": 423},
    }

    def lists():
        theory = demonstration_theory()
        goal = Equation(RA(V("xs"), N()), R(V("xs")))
        before = theory.search(goal, "xs") is not None
        discovery = discover_accumulator_lemma(theory, goal)
        assert discovery.certificate is not None
        assert theory.install("revacc_spec", discovery.certificate)
        after = theory.search(goal, "xs")
        assert after is not None
        assert theory.install("revacc_original", after)
        payload = [{"name": name, "certificate": cert.to_json()} for name, cert in theory.certificates.items()]
        (certificates / "induction.json").write_text(json.dumps(payload, indent=2) + "\n")
        return {"induction_certificates": len(payload), "fixed_goal_before_generalization": before,
                "fixed_goal_after_generalization": True, "candidates_enumerated": discovery.enumerated,
                "finite_test_survivors": discovery.sample_survivors,
                "generalized_equation": str(discovery.equation),
                "changed_recursive_argument_indices": list(discovery.changed_arguments),
                "proof_rewrite_steps": {name: sum(len(getattr(case, side)) for case in (cert.base, cert.step)
                                                    for side in ("left", "right"))
                                        for name, cert in theory.certificates.items()}}
    results["induction"], results["induction_seconds"] = measured(lists)

    def recurrences():
        rng, cases = random.Random(420), []
        x = Poly.variable(1, 0)
        inputs = [(f"power_sum_{k}", (x + 1) ** k, Q(0)) for k in range(1, 6)]
        for i in range(60):
            degree = i % 7
            f = Poly.make(1, [((k,), Q(rng.randrange(-8, 9), rng.randrange(1, 6))) for k in range(degree + 1)])
            inputs.append((f"random_{i:02d}", f, Q(rng.randrange(-10, 11), 3)))
        for name, f, initial in inputs:
            r = synthesize_recurrence(f, initial, max_degree=8)
            ok = r.polynomial is not None and check_recurrence(f, initial, r.polynomial)
            assert ok, name
            cases.append({"name": name, "increment": f.to_json(), "initial": str(initial),
                          "candidate": r.polynomial.to_json(), "checked": ok, "candidates": r.candidates,
                          "counterexamples": r.counterexamples, "inconsistent_degrees": r.inconsistent_degrees})
        (certificates / "recurrences.json").write_text(json.dumps(cases, indent=2) + "\n")
        return {"cases": len(cases), "certified": sum(c["checked"] for c in cases),
                "total_candidates": sum(c["candidates"] for c in cases),
                "total_step_counterexamples": sum(len(c["counterexamples"]) for c in cases),
                "named_formulas": {c["name"]: str(Poly.from_json(c["candidate"])) for c in cases[:5]}}
    results["recurrence"], results["recurrence_seconds"] = measured(recurrences)

    def affine_to_json(a):
        return {"coefficients": list(map(str, a.coefficients)), "constant": str(a.constant)}

    def witnesses():
        rng, inputs, cases = random.Random(421), [], []
        inputs.append(("unbounded_strip", WitnessProblem(1, 1, (), (Affine.make([-1, 1], -1), Affine.make([1, -1], 2)))))
        inputs.append(("domain_cone", WitnessProblem(1, 1, (Affine.make([1]),), (Affine.make([-1, 1]), Affine.make([2, -1])))))
        inputs.append(("bounded_max", WitnessProblem(1, 1, (Affine.make([1]), Affine.make([-1], 1)),
                      (Affine.make([-1, 1]), Affine.make([1, 1], -1), Affine.make([0, -1], 1)))))
        for case in range(40):
            n, m = 1 + case % 3, 1 + case % 2
            matrix = [[Q(rng.randrange(-5, 6)) for _ in range(n)] for _ in range(m)]
            offsets = [Q(rng.randrange(-5, 6), 3) for _ in range(m)]
            goals = []
            for i in range(m):
                out = [Q(int(j == i)) for j in range(m)]
                coeffs = [-a for a in matrix[i]] + out
                goals += [Affine.make(coeffs, -offsets[i]), Affine.make([-c for c in coeffs], offsets[i])]
            inputs.append((f"forced_affine_{case:02d}", WitnessProblem(n, m, (), tuple(goals))))
        for case in range(20):
            n, m = 2, 2
            domain = tuple(Affine.make([int(i == j) * sign for j in range(n)], int(sign < 0))
                           for i in range(n) for sign in (1, -1))
            mat = [[Q(rng.randrange(-4, 5)) for _ in range(n)] for _ in range(m)]
            off = [Q(rng.randrange(-3, 4)) for _ in range(m)]
            goals = []
            for _ in range(5):
                d = [Q(rng.randrange(-2, 3)) for _ in range(m)]
                lam = [Q(rng.randrange(3)) for _ in domain]
                coeffs = [sum(l * g.coefficients[j] for l, g in zip(lam, domain)) - sum(d[k] * mat[k][j] for k in range(m))
                          for j in range(n)] + d
                const = Q(rng.randrange(2)) + sum(l * g.constant for l, g in zip(lam, domain)) - sum(d[k] * off[k] for k in range(m))
                goals.append(Affine.make(coeffs, const))
            inputs.append((f"polyhedral_{case:02d}", WitnessProblem(n, m, domain, tuple(goals))))
        for name, problem in inputs:
            cert = synthesize_witness(problem)
            ok = cert is not None and check_witness(problem, cert)
            assert ok, name
            cases.append({"name": name, "inputs": problem.inputs, "outputs": problem.outputs,
                          "domain": list(map(affine_to_json, problem.domain)), "goals": list(map(affine_to_json, problem.goals)),
                          "certificate": cert.to_json(), "checked": ok})
        constant_ok = synthesize_witness(inputs[0][1], constant_only=True) is not None
        (certificates / "witnesses.json").write_text(json.dumps(cases, indent=2) + "\n")
        return {"cases": len(cases), "certified": sum(c["checked"] for c in cases),
                "strip_constant_template_certified": constant_ok, "strip_affine_template_certified": True,
                "strip_witness": cases[0]["certificate"]["witnesses"]}
    results["witness"], results["witness_seconds"] = measured(witnesses)

    def sos():
        rng, cases = random.Random(422), []
        x, y = Poly.variable(2, 0), Poly.variable(2, 1)
        roots = square_dictionary(2, 2)
        for i in range(40):
            constraints = [x, 1 - x, y, 1 - y] if i % 2 else []
            p = Poly.constant(2, 0)
            for _ in range(6):
                q = rng.choice(roots)
                g = rng.choice([Poly.constant(2, 1), *constraints])
                p += Q(rng.randrange(1, 6), rng.randrange(1, 4)) * q ** 2 * g
            cert = search_sos(p, roots, constraints)
            ok = cert is not None and check_sos(p, constraints, cert)
            assert ok, i
            cases.append({"name": f"constructed_{i:02d}", "target": p.to_json(), "constraints": [g.to_json() for g in constraints],
                          "certificate": cert.to_json(), "checked": ok})
        (certificates / "sos.json").write_text(json.dumps(cases, indent=2) + "\n")
        motzkin = x ** 4 * y ** 2 + x ** 2 * y ** 4 + 1 - 3 * x ** 2 * y ** 2
        return {"cases": len(cases), "certified": sum(c["checked"] for c in cases),
                "dictionary_roots": len(roots), "constructed_from_same_dictionary": True,
                "motzkin_plain_dictionary_certificate_found": search_sos(motzkin, square_dictionary(2, 3)) is not None}
    results["sos"], results["sos_seconds"] = measured(sos)

    def bernstein():
        rng, cases = random.Random(423), []
        x = Poly.variable(1, 0)
        inputs = [("midpoint_well", (x - Q(1, 2)) ** 2 + Q(1, 100))]
        for i in range(20):
            a, b = Q(rng.randrange(-4, 5)), Q(rng.randrange(-4, 5), 3)
            inputs.append((f"univariate_{i:02d}", (a * x + b) ** 2 + Q(1, 10)))
        x, y = Poly.variable(2, 0), Poly.variable(2, 1)
        for i in range(20):
            p = Poly.constant(2, Q(1, 4))
            for _ in range(2):
                a, b, c = [Q(rng.randrange(-2, 3)) for _ in range(3)]
                p += (a * x + b * y + c) ** 2
            inputs.append((f"bivariate_{i:02d}", p))
        for name, p in inputs:
            box = [(Q(0), Q(1))] * p.n
            root = search_bernstein(p, box, max_depth=0, strict=True)
            r = search_bernstein(p, box, max_depth=12, strict=True)
            ok = r.status == "certified" and check_bernstein(p, box, r.tree, strict=True)
            assert ok, (name, r.status)
            cases.append({"name": name, "target": p.to_json(), "box": [[str(a), str(b)] for a, b in box],
                          "strict": True, "tree": r.tree, "checked": ok, "root_only_certified": root.status == "certified",
                          "visited": r.visited, "leaves": r.leaves, "depth": r.deepest})
        (certificates / "bernstein.json").write_text(json.dumps(cases, indent=2) + "\n")
        diagonal = search_bernstein((x - y) ** 2, [(0, 1)] * 2, max_depth=4)
        return {"cases": len(cases), "certified": sum(c["checked"] for c in cases),
                "root_only_certified": sum(c["root_only_certified"] for c in cases),
                "total_leaves": sum(c["leaves"] for c in cases), "max_depth": max(c["depth"] for c in cases),
                "diagonal_square_at_depth_4": diagonal.status}
    results["bernstein"], results["bernstein_seconds"] = measured(bernstein)

    results["total_certificate_cases"] = sum(results[key]["certified"] for key in ("recurrence", "witness", "sos", "bernstein")) + results["induction"]["induction_certificates"]
    (output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parent.parent / "results")
    run(parser.parse_args().output)
