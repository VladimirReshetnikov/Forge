#!/usr/bin/env python3
"""Regenerate the derived cross-run views under results/.

Reads the twenty-seven recorded runs under proposals/<slug>/results/ -- the
design round p1..p9, the extension round e1..e9, and the third round r1..r9 --
and writes:

    results/manifest.json          one row per run
    results/certificate-counts.csv per run, per family

Nothing here edits a recorded run. The derived files always carry `run` and
`round` columns, and certificate-counts.csv deliberately emits no grand total:
the twenty-seven runs used different seeds, generators, case sets and units,
their counts are not commensurable within a round, and the rounds attack
overlapping problems so a cross-round total would double-count. Worse, the
shared seed value 20260915 now appears in two different rounds over unrelated
generators, so matching seeds are not even evidence of a shared corpus. See
results/README.md.

The `outcome` column matters as much as the counts. A row whose expected
outcome is `refuted` and whose `achieved` equals its `cases` is a fully
successful row: a worker that returns a counterexample has answered the
question. Reading such a row as a failure -- or omitting it to improve an
apparent success rate -- is the specific mistake this file exists to prevent.
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

EXTENSION_RUNS: list[dict] = [
    {
        "run": "e1",
        "slug": "e1-relational-closure",
        "emphasis": "span and ideal lanes over one problem set",
        "seed": 20260915,
        "test_framework": "unittest",
        "test_count": 40,
        "test_unit": "tests",
        "certificates": 108,
        "certificate_layout": "one experiment directory with per-group summaries",
        "replay": "108/108 under python -S, search and SymPy unimported",
        "pdf_pages": 27,
        "families": [
            # (family, outcome, cases, achieved, ablation_achieved)
            # Ablation column is the LINEAR-span lane; the main column is the
            # ideal lane. The two families with 0 are the point of the run.
            ("scaled_graph", "certified", 8, 8, 8),
            ("coupled_nonlinear", "certified", 8, 8, 0),
            ("nonlinear_equivalence", "certified", 8, 8, 0),
            ("nonlinear_mutant", "refuted", 8, 8, 8),
            ("affine_equivalence", "certified", 12, 12, 12),
            ("affine_mutant", "refuted", 6, 6, 6),
            ("control_flow", "certified", 4, 4, 4),
            ("boundary_controls", "mixed", 8, 8, 8),
        ],
    },
    {
        "run": "e2",
        "slug": "e2-algorithmic-extensions",
        "emphasis": "inductive subspaces, Gosper and creative telescoping",
        "seed": 20260915,
        "test_framework": "unittest",
        "test_count": 13,
        "test_unit": "test methods (69 subtests)",
        "certificates": 65,
        "certificate_layout": "one certificates.json, four families",
        "replay": "stdlib replay, return code 0",
        "pdf_pages": 30,
        "families": [
            ("two_sided", "certified", 25, 25, None),
            # ablation column: conservation-only lane on the same features
            ("invariant", "certified", 24, 24, 3),
            ("gosper", "certified", 15, 15, None),
            ("telescoper", "certified", 1, 1, None),
        ],
    },
    {
        "run": "e3",
        "slug": "e3-closure-extensions",
        "emphasis": "four lanes; an independent oracle on every finite-state case",
        "seed": 20260915,
        "test_framework": "unittest",
        "test_count": 12,
        "test_unit": "test methods (313 subtests)",
        "certificates": 313,
        "certificate_layout": "per-case bundles under results/certificates/",
        "replay": "stdlib replay of every bundle",
        "pdf_pages": 35,
        "families": [
            ("finite_state", "mixed", 240, 240, None),
            ("finite_state_ablation", "refuted", 1, 1, None),
            ("finite_state_budget", "unknown", 1, 0, None),
            ("ideal_generated", "certified", 16, 16, None),
            ("ideal_named", "certified", 2, 2, None),
            ("ideal_negative", "refuted", 1, 1, None),
            ("telescoping", "certified", 10, 10, None),
            ("telescoping_budget", "unknown", 2, 0, None),
            ("vector_generated", "certified", 24, 24, None),
            ("vector_named", "certified", 2, 2, None),
            ("vector_negative", "refuted", 17, 17, None),
            ("vector_ablation", "unknown", 1, 0, None),
        ],
    },
    {
        "run": "e4",
        "slug": "e4-delta-countermodels",
        "emphasis": "finite Kripke countermodels; polynomial-machine reachability",
        "seed": 20260915,
        "test_framework": "pytest",
        "test_count": 151,
        "test_unit": "tests",
        "certificates": 73,
        "certificate_layout": "one corpus.json plus per-trial records",
        "replay": "replay.py over the stored corpus",
        "pdf_pages": 32,
        "families": [
            ("machine", "mixed", 66, 65, None),
            ("ipc_countermodel", "refuted", 16, 8, None),
        ],
    },
    {
        "run": "e5",
        "slug": "e5-finite-certificates",
        "emphasis": "observable-space closure with the sharp D-1 bound",
        "seed": 2026091507,
        "test_framework": "pytest",
        "test_count": 117,
        "test_unit": "test items",
        "certificates": 55,
        "certificate_layout": "certificates/ and counterexamples/ directories",
        "replay": "stdlib replay; 818 mutations generated, 0 accepted",
        "pdf_pages": 29,
        "families": [
            ("linear", "mixed", 36, 36, None),
            ("ideal", "mixed", 13, 12, None),
            ("binomial_sum", "certified", 10, 7, None),
        ],
    },
    {
        "run": "e6",
        "slug": "e6-finite-certificates-b",
        "emphasis": "three lanes reported by outcome kind, not success rate",
        "seed": 20260915,
        "test_framework": "pytest",
        "test_count": 318,
        "test_unit": "tests",
        "certificates": 78,
        "certificate_layout": "one certificates.json",
        "replay": "78 accepted under python -S",
        "pdf_pages": 34,
        "families": [
            ("ideal", "certified", 29, 27, None),
            ("weighted", "mixed", 48, 48, None),
            ("telescoping", "certified", 5, 3, None),
        ],
    },
    {
        "run": "e7",
        "slug": "e7-capability-extensions",
        "emphasis": "continuation-local synthesis; cyclic descent; ideal completion",
        "seed": "fixed per experiment; SymPy validation seeded separately",
        "test_framework": "unittest",
        "test_count": 29,
        "test_unit": "test methods (140 subtests)",
        "certificates": 135,
        "certificate_layout": "one certificates.json, five record kinds",
        "replay": "135 accepted by the standalone replayer; 31 corruptions rejected",
        "pdf_pages": 30,
        "families": [
            ("constant_action_invariant", "certified", 113, 113, None),
            ("ideal_preservation", "certified", 14, 14, None),
            ("ranking", "certified", 4, 4, None),
            ("indexing_algebra", "certified", 1, 1, None),
            ("orbit_counterexample", "refuted", 3, 3, None),
        ],
    },
    {
        "run": "e8",
        "slug": "e8-invariant-ideals",
        "emphasis": "bounded-multiplier invariants, finite covers, integer projection",
        "seed": "fixed per lane",
        "test_framework": "unittest",
        "test_count": 21,
        "test_unit": "test methods (19 mutation cases)",
        "certificates": 422,
        "certificate_layout": "one certificates.json, four lanes",
        "replay": "422/422 with search entry points replaced by exceptions",
        "pdf_pages": 31,
        "families": [
            ("constant_multipliers", "certified", 51, 51, None),
            ("polynomial_multipliers", "certified", 14, 14, None),
            ("finite_algebra", "mixed", 136, 136, None),
            ("integer_projection", "certified", 221, 221, None),
        ],
    },
    {
        "run": "e9",
        "slug": "e9-finite-summaries",
        "emphasis": "weighted words, boundary-safe telescoping, Ore transport",
        "seed": 681437,
        "test_framework": "unittest",
        "test_count": 41,
        "test_unit": "tests",
        "certificates": 245,
        "certificate_layout": "results/run-4/certificates.json",
        "replay": "245/245 under python -S with SymPy absent; 245 mutations rejected",
        "pdf_pages": 30,
        "families": [
            ("matrix_closure", "certified", 54, 54, None),
            ("separating_word", "refuted", 115, 115, None),
            ("telescoper", "certified", 23, 23, None),
            ("ore_identity", "certified", 6, 6, None),
            ("singularity_seed_plan", "certified", 47, 47, None),
        ],
    },
]

THIRD_RUNS: list[dict] = [
    {
        "run": "r1",
        "slug": "r1-grammar-closure",
        "emphasis": "many-sorted multilinear closure; observable quotients",
        "seed": "ranges 10000-10239 and 20000-20039",
        "test_framework": "unittest",
        "test_count": 18,
        "test_unit": "test methods",
        "certificates": 8,
        "certificate_layout": "named fixtures with per-fixture records",
        "replay": "8/8 in isolated processes containing only the checker",
        "pdf_pages": None,
        "families": [
            ("differential_finite_language", "mixed", 240, 240, None),
            ("quotient", "certified", 40, 40, None),
            ("invalid_objects", "refuted", 20, 20, None),
            ("resource_cutoff", "unknown", 3, 0, None),
        ],
    },
    {
        "run": "r2",
        "slug": "r2-noncommutative",
        "emphasis": "two-sided receipts without completion; word Gram matrices",
        "seed": 2026091503,
        "test_framework": "unittest",
        "test_count": 57,
        "test_unit": "test methods (one holding 24 subtests)",
        "certificates": 119,
        "certificate_layout": "one certificates.json",
        "replay": "119/119, producer imports blocked, site packages disabled",
        "pdf_pages": None,
        "families": [
            ("object_language_queries", "mixed", 90, 90, None),
            ("countermodels", "refuted", 20, 20, None),
            ("further_records", "certified", 9, 9, None),
        ],
    },
    {
        "run": "r3",
        "slug": "r3-three-engines",
        "emphasis": "polyhedral projection; bounded completion; analytic jets",
        "seed": 20260915,
        "test_framework": "unittest",
        "test_count": 12,
        "test_unit": "test methods",
        "certificates": 228,
        "certificate_layout": "one certificates.json, three lanes",
        "replay": "228 accepted; 11 unknowns correctly not accepted",
        "pdf_pages": None,
        "families": [
            ("polyhedral", "mixed", 110, 109, None),
            ("noncommutative", "certified", 85, 82, None),
            ("analytic", "certified", 44, 37, None),
        ],
    },
    {
        "run": "r4",
        "slug": "r4-analytic-certificates",
        "emphasis": "ladders with ghost rates; ascending-order dominance",
        "seed": 20260915,
        "test_framework": "unittest",
        "test_count": 18,
        "test_unit": "test methods",
        "certificates": 284,
        "certificate_layout": "one certificates.json plus an index",
        "replay": "284/284, search not imported, site packages disabled",
        "pdf_pages": None,
        "families": [
            ("random_eventual_sign", "certified", 240, 240, None),
            ("boundary_zero", "certified", 25, 25, None),
            ("named", "certified", 8, 8, None),
            ("auxiliary_factors", "certified", 4, 4, None),
            ("compact_cover", "certified", 4, 4, None),
            ("growth_witness", "certified", 2, 2, None),
            ("counterexample", "refuted", 1, 1, None),
        ],
    },
    {
        "run": "r5",
        "slug": "r5-analytic-extensions",
        "emphasis": "anchored remainders; series barriers and divergence",
        "seed": None,
        "test_framework": "unittest",
        "test_count": 25,
        "test_unit": "test methods",
        "certificates": 246,
        "certificate_layout": "run-01 directory, four record kinds",
        "replay": "246/246 over 230 distinct subjects, search blocked",
        "pdf_pages": None,
        "families": [
            ("barrier", "certified", 81, 81, None),
            ("anchored", "certified", 62, 62, None),
            ("divergence", "certified", 60, 60, None),
            ("ladder", "certified", 43, 43, None),
        ],
    },
    {
        "run": "r6",
        "slug": "r6-flow-ladders",
        "emphasis": "fixed-alphabet ladders; shortest-ladder minimality receipts",
        "seed": None,
        "test_framework": "unittest",
        "test_count": 22,
        "test_unit": "test methods",
        "certificates": 304,
        "certificate_layout": "accepted/ directory",
        "replay": "304/304, discovery modules not loaded",
        "pdf_pages": None,
        "families": [
            ("positive", "certified", 196, 196, None),
            ("negative_point", "refuted", 44, 44, None),
            ("system", "certified", 40, 40, None),
            ("root", "certified", 16, 16, None),
            ("grammar_obstruction", "refuted", 8, 8, None),
        ],
    },
    {
        "run": "r7",
        "slug": "r7-quantitative",
        "emphasis": "six exact quantitative workers; the moment-transfer correction",
        "seed": 20260915,
        "test_framework": "unittest",
        "test_count": 24,
        "test_unit": "test methods (also run under -O -S)",
        "certificates": 520,
        "certificate_layout": "one certificates.json, six workers",
        "replay": "520 accepted, 520 mutations rejected, oracles forbidden",
        "pdf_pages": None,
        "families": [
            ("quantitative_workers", "certified", 520, 520, None),
        ],
    },
    {
        "run": "r8",
        "slug": "r8-alternation-probability",
        "emphasis": "parity games; couplings with Hall and Farkas duals",
        "seed": None,
        "test_framework": "unittest",
        "test_count": 14,
        "test_unit": "regression methods",
        "certificates": 1564,
        "certificate_layout": "full/ and smoke/ corpora, kept separate",
        "replay": "1,564 records, search imports forbidden",
        "pdf_pages": 31,
        "families": [
            ("parity", "mixed", 884, 884, None),
            ("transport", "certified", 400, 400, None),
            ("mdp", "mixed", 180, 180, None),
            ("simulation", "mixed", 100, 100, None),
        ],
    },
    {
        "run": "r9",
        "slug": "r9-infinite-horizon",
        "emphasis": "pushdown summaries; Buchi duals; properness potentials",
        "seed": 20260915,
        "test_framework": "unittest",
        "test_count": 36,
        "test_unit": "test methods",
        "certificates": 28566,
        "certificate_layout": "one certificates.json",
        "replay": "28,566 records, no search module imported",
        "pdf_pages": None,
        "families": [
            # 39 of the 250 pds_general cases were left UNSETTLED by a bounded
            # oracle. They are recorded, not counted as corroboration.
            ("games", "mixed", 22300, 22300, None),
            ("markov_chains", "mixed", 970, 970, None),
            ("pushdown", "mixed", 881, 842, None),
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


EXTENSION_ENVIRONMENT = {
    "date": "2026-09-15",
    "python": "3.13.5",
    "sympy": "1.14.0",
    "platform": "Linux-6.18.44-x86_64-with-glibc2.41",
    "prepared_against_forge_revision": (
        "674521027d968d59f7b83220ed52304a85cb55e2"
    ),
    "note": (
        "Five of these nine recorded the seed value 20260915, one day after the "
        "design round's shared 20260914. The coincidence means as little as it "
        "did the first time: the same seed drives different generators over "
        "different case sets."
    ),
    "rerun_in_merge_environment": "results/extension-suites-rerun.json",
}


THIRD_ENVIRONMENT = {
    "date": "2026-09-15",
    "python": "3.13.5",
    "platform": "Linux-6.18.44-x86_64-with-glibc2.41",
    "prepared_against_forge_revision": (
        "c98e47c5f804e92880fc1d0e378c1b95832b685c"
    ),
    "note": (
        "Four of these nine recorded the seed value 20260915 -- which is also "
        "the extension round's shared value. The same integer now labels runs "
        "in two different rounds over unrelated generators, so a matching seed "
        "is not even evidence of a shared corpus."
    ),
    "rerun_in_merge_environment": "results/round-three-suites-rerun.json",
    "traps_documented_in_article_section_13": [
        "r7 pilot and final summaries report identical records/mutations/seed "
        "but are different runs",
        "r8 smoke and full reports both state exhaustive_parity_arenas: 584; "
        "it is the same 584",
        "r9 distinguishes arenas (22,300), region records (26,915) and "
        "start-state replays (67,260)",
    ],
}


def lean_status(slug: str) -> dict:
    """Find whatever that run recorded about Lean, under any of its filenames."""
    directory = PROPOSALS / slug / "results"
    # p6 keeps its artefact status at the proposal root, e8 beside its Lean
    # sources. Look in all three places rather than reporting "prose only".
    search_roots = (
        directory,
        PROPOSALS / slug,
        PROPOSALS / slug / "lean",
        PROPOSALS / slug / "docs",
    )
    for name in (
        "lean_status.json",
        "lean-status.json",
        "lean_comparisons.json",
        "lean-generation.json",
        "status.json",
        "summary.json",
        "run.json",
        "artifact_validation.json",
        "artifact-validation.json",
        "artifact-qa.json",
        "ARTIFACT_STATUS.json",
        "results.json",
        "environment.json",
        "experiment-summary.json",
        "LEAN-STATUS.json",
        "run-01/summary.json",
        "accepted/summary.json",
        "examples/summary.json",
        "full/report.json",
    ):
        for root in search_roots:
            path = root / name
            if path.exists():
                break
        else:
            continue
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (ValueError, OSError):
            continue
        name = path.relative_to(PROPOSALS / slug).as_posix()
        # r7 records one row per lane rather than a single object.
        if isinstance(data, list):
            statuses = sorted({
                r.get("status") for r in data
                if isinstance(r, dict) and r.get("status")
            })
            if statuses:
                return {"file": name, "field": "[].status", "value": statuses}
            continue
        # Lean-specific keys first: several files carry a generic "status"
        # describing the whole run, which is not what this function reports.
        for key in (
            "lean_status",
            "lean_compilation",
            "lean_compiled",
            "lean_examples_compiled",
            "lean_core_specimens",
            "lean_executed",
            "lean",
            "lean_kernel_checks",
            "status",
            # Last resort: r3 states it in a prose "evidence" field.
            "evidence",
        ):
            if key in data:
                return {"file": name, "field": key, "value": data[key]}
        nested = data.get("environment")
        if isinstance(nested, dict) and "lean_status" in nested:
            return {
                "file": name,
                "field": "environment.lean_status",
                "value": nested["lean_status"],
            }
        meta = data.get("metadata")
        if isinstance(meta, dict) and "lean_available" in meta:
            return {
                "file": name,
                "field": "metadata.lean_available",
                "value": meta["lean_available"],
            }
        # e1 records one row per file rather than a single status field.
        rows = data.get("results")
        if isinstance(rows, list) and rows and isinstance(rows[0], dict):
            statuses = {r.get("status") for r in rows if "status" in r}
            if statuses:
                return {
                    "file": name,
                    "field": "results[].status",
                    "value": sorted(x for x in statuses if x is not None),
                }
    return {"file": None, "field": None, "value": "recorded in prose only"}


def main() -> int:
    RESULTS.mkdir(exist_ok=True)

    manifest = {
        "note": (
            "Derived index over the twenty-seven recorded runs. The runs "
            "themselves are under proposals/<slug>/results/ and are never "
            "modified. Counts are per run and are not commensurable across "
            "runs, nor across the three rounds."
        ),
        "design_round_environment": COMMON_ENVIRONMENT,
        "extension_round_environment": EXTENSION_ENVIRONMENT,
        "third_round_environment": THIRD_ENVIRONMENT,
        "lean": {
            "all_twenty_seven_runs": (
                "NOT_RUN -- no lean/lake executable available"
            ),
            "this_merge_merged_tree": "results/lean-core-elaboration.json",
            "this_merge_extensions": "results/lean-extensions-elaboration.json",
            "this_merge_third_round": (
                "results/lean-round-three-elaboration.json -- 2 elaborated, "
                "1 failed to parse"
            ),
        },
        "runs": [],
    }

    for round_name, entries in (("design", RUNS),
                                ("extension", EXTENSION_RUNS),
                                ("third", THIRD_RUNS)):
        for entry in entries:
            record = {"round": round_name}
            record.update({k: v for k, v in entry.items() if k != "families"})
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
            [
                "run",
                "round",
                "slug",
                "family",
                "outcome",
                "cases",
                "achieved",
                "ablation_achieved",
            ]
        )
        for entry in RUNS:
            for family, cases, ok, ablation in entry["families"]:
                writer.writerow(
                    [
                        entry["run"],
                        "design",
                        entry["slug"],
                        family,
                        "certified",
                        cases,
                        ok,
                        "" if ablation is None else ablation,
                    ]
                )
        for entry in EXTENSION_RUNS:
            for family, outcome, cases, ok, ablation in entry["families"]:
                writer.writerow(
                    [
                        entry["run"],
                        "extension",
                        entry["slug"],
                        family,
                        outcome,
                        cases,
                        ok,
                        "" if ablation is None else ablation,
                    ]
                )
        for entry in THIRD_RUNS:
            for family, outcome, cases, ok, ablation in entry["families"]:
                writer.writerow(
                    [
                        entry["run"],
                        "third",
                        entry["slug"],
                        family,
                        outcome,
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
