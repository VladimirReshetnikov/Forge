#!/usr/bin/env python3
"""Regenerate the derived cross-run views under results/.

Reads the nine recorded runs under proposals/<slug>/results/ and writes:

    results/manifest.json          one row per run
    results/certificate-counts.csv per run, per family

Nothing here edits a recorded run. The derived files always carry a `run`
column, and certificate-counts.csv deliberately emits no grand total: the nine
runs used different seeds, generators and case sets, and their counts are not
commensurable. See results/README.md.
"""

from __future__ import annotations

import csv
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROPOSALS = ROOT / "proposals"
RESULTS = ROOT / "results"

# Facts that are not recoverable by parsing -- they come from each run's own
# prose and status files, and are recorded here so the manifest is complete.
RUNS: list[dict] = [
    {
        "run": "p1",
        "slug": "p1-structural-search",
        "emphasis": "six certificate families under one measurement protocol",
        "seed": None,
        "test_framework": "pytest",
        "test_count": 275,
        "test_unit": "test instances",
        "certificates": 198,
        "certificate_layout": "single list file",
        "replay": "198/198, standard-library-only decoder",
        "pdf_pages": 31,
        "families": [
            ("quadratic_sos", 60, 60, 1),
            ("finite_cone_lp", 17, 17, 0),
            ("bernstein_box", 18, 18, 1),
            ("polynomial_recurrence", 33, 33, None),
            ("integral_affine_witness", 40, 40, None),
            ("univariate_with_zeros", 30, 30, 0),
        ],
    },
    {
        "run": "p2",
        "slug": "p2-obligation-controller",
        "emphasis": "obligation controller; per-family seeds",
        "seed": "420/421/422/423 (per family)",
        "test_framework": "unittest",
        "test_count": 31,
        "test_unit": "test methods",
        "certificates": 215,
        "certificate_layout": "five family-bundled lists",
        "replay": "215/215",
        "pdf_pages": None,
        "families": [
            ("list_induction", 6, 6, None),
            ("polynomial_recurrence", 65, 65, None),
            ("affine_witness_farkas", 63, 63, None),
            ("dictionary_square", 40, 40, None),
            ("bernstein_box", 41, 41, 25),
        ],
    },
    {
        "run": "p3",
        "slug": "p3-planner-certificate-layer",
        "emphasis": "assertion-counted mechanism ablations",
        "seed": "20260914",
        "test_framework": "assertions in driver",
        "test_count": 1680,
        "test_unit": "assertions",
        "certificates": 24,
        "certificate_layout": "24 individual files",
        "replay": "24/24, CHECKED_PYTHON",
        "pdf_pages": 33,
        "families": [
            ("quadratic_constructed", 60, 60, None),
            ("quadratic_curated", 4, 4, None),
            ("cone_constructed", 30, 30, None),
            ("cone_curated", 10, 9, 0),
            ("bernstein_box", 10, 8, 3),
            ("horn_demand", 12, 12, 3),
            ("list_induction", 8, 8, 6),
        ],
    },
    {
        "run": "p4",
        "slug": "p4-theory-cooperation",
        "emphasis": "largest artefact corpus; theory cooperation",
        "seed": "20260914",
        "test_framework": "pytest",
        "test_count": 64,
        "test_unit": "tests",
        "certificates": 1238,
        "certificate_layout": "single list file",
        "replay": "1238/1238, re-verified from an extracted archive copy",
        "pdf_pages": 32,
        "families": [
            ("residue_witness", 1080, 831, None),
            ("cdclt_random", 300, 300, None),
            ("cone_ideal", 49, 47, None),
            ("quadratic", 40, 40, None),
            ("bernstein_box", 13, 12, None),
            ("pigeonhole", 5, 5, None),
            ("structural_equations", 7, 5, None),
            ("induction_ablation", 4, 1, None),
        ],
    },
    {
        "run": "p5",
        "slug": "p5-certificate-first",
        "emphasis": "expected-outcome benchmarking with negative controls",
        "seed": "20260914",
        "test_framework": "pytest",
        "test_count": 73,
        "test_unit": "tests",
        "certificates": 58,
        "certificate_layout": "two list files (exported subset)",
        "replay": "58/58 re-accepted on reload",
        "pdf_pages": 30,
        "families": [
            ("cone_named", 12, 9, None),
            ("cone_generated", 100, 100, None),
            ("false_controls", 24, 0, None),
            ("bernstein_box", 45, 43, None),
            ("recurrence_invariant", 49, 49, None),
        ],
    },
    {
        "run": "p6",
        "slug": "p6-proof-logging-cdcl",
        "emphasis": "proof-logging CDCL(T) with independent RUP replay",
        "seed": "20260914",
        "test_framework": "assertions in driver",
        "test_count": 1500,
        "test_unit": "differential cases",
        "certificates": 22,
        "certificate_layout": "22 individual files",
        "replay": "all valid under python -S; 3 unknowns skipped explicitly",
        "pdf_pages": 33,
        "families": [
            ("sat_differential", 1500, 1500, None),
            ("sat_unsat_certificates", 222, 222, None),
            ("polynomial_search", 10, 7, None),
            ("invariant_synthesis", 6, 6, None),
        ],
    },
    {
        "run": "p7",
        "slug": "p7-successor-architecture",
        "emphasis": "integer lattices; component cases with corruption controls",
        "seed": "20260914",
        "test_framework": "assertions in driver",
        "test_count": 833,
        "test_unit": "component cases",
        "certificates": 26,
        "certificate_layout": "26 individual files",
        "replay": "26/26 under python -S",
        "pdf_pages": 38,
        "families": [
            ("sos_cone", 9, 9, None),
            ("accumulator_invariant", 11, 11, None),
            ("integer_lattice", 5, 5, None),
            ("horn_demand", 1, 1, None),
        ],
    },
    {
        "run": "p8",
        "slug": "p8-obligation-broker",
        "emphasis": "cleanest dictionary ablation; largest Horn workload",
        "seed": None,
        "test_framework": "pytest",
        "test_count": 260,
        "test_unit": "tests",
        "certificates": 2,
        "certificate_layout": "2 individual files",
        "replay": "in-process only; no standalone verifier shipped",
        "pdf_pages": 24,
        "families": [
            ("cone_enriched", 60, 60, 17),
            ("bernstein_box", 21, 21, 0),
            ("affine_invariant", 121, 121, None),
            ("out_of_template", 5, 0, None),
        ],
    },
    {
        "run": "p9",
        "slug": "p9-proof-planner",
        "emphasis": "small, heavily mutation-tested; checker wider than searcher",
        "seed": None,
        "test_framework": "pytest",
        "test_count": 69,
        "test_unit": "tests",
        "certificates": 13,
        "certificate_layout": "13 bundles in one list file",
        "replay": "13/13 under python -S",
        "pdf_pages": 31,
        "families": [
            ("theorem_bank", 1, 1, None),
            ("horn_proof", 4, 4, None),
            ("cone", 6, 6, None),
            ("box", 1, 1, None),
            ("witness", 1, 1, None),
        ],
    },
]

COMMON_ENVIRONMENT = {
    "date": "2026-09-14",
    "python": "3.13.5",
    "numpy": "2.3.5",
    "scipy": "1.17.0",
    "sympy": "1.14.0",
    "platform": "Linux x86-64",
    "note": (
        "Identical environments and a shared seed value across five runs do NOT "
        "make the runs comparable: the same seed drives different generators "
        "over different case sets."
    ),
}


def lean_status(slug: str) -> dict:
    """Find whatever that run recorded about Lean, under any of its filenames."""
    directory = PROPOSALS / slug / "results"
    for name in (
        "lean_status.json",
        "lean-status.json",
        "lean_comparisons.json",
        "status.json",
        "artifact_validation.json",
        "ARTIFACT_STATUS.json",
    ):
        path = directory / name
        if not path.exists():
            continue
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (ValueError, OSError):
            continue
        for key in (
            "status",
            "lean_compilation",
            "lean_compiled",
            "lean_examples_compiled",
        ):
            if key in data:
                return {"file": name, "field": key, "value": data[key]}
    return {"file": None, "field": None, "value": "recorded in prose only"}


def main() -> int:
    RESULTS.mkdir(exist_ok=True)

    manifest = {
        "note": (
            "Derived index over the nine recorded runs. The runs themselves are "
            "under proposals/<slug>/results/ and are never modified. Counts are "
            "per run and are not commensurable across runs."
        ),
        "common_environment": COMMON_ENVIRONMENT,
        "lean": {
            "all_nine_runs": "NOT_RUN -- no lean/lake executable available",
            "this_merge": "results/lean-core-elaboration.json",
        },
        "runs": [],
    }

    for entry in RUNS:
        record = {k: v for k, v in entry.items() if k != "families"}
        record["results_path"] = f"proposals/{entry['slug']}/results"
        record["lean_status_recorded"] = lean_status(entry["slug"])
        record["family_count"] = len(entry["families"])
        manifest["runs"].append(record)

    (RESULTS / "manifest.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
    )

    with (RESULTS / "certificate-counts.csv").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.writer(handle)
        writer.writerow(
            ["run", "slug", "family", "cases", "succeeded", "ablation_succeeded"]
        )
        for entry in RUNS:
            for family, cases, ok, ablation in entry["families"]:
                writer.writerow(
                    [
                        entry["run"],
                        entry["slug"],
                        family,
                        cases,
                        ok,
                        "" if ablation is None else ablation,
                    ]
                )
        # Deliberately no total row. See results/README.md.

    print(f"wrote {RESULTS / 'manifest.json'}")
    print(f"wrote {RESULTS / 'certificate-counts.csv'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
