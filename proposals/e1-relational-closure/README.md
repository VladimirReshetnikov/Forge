# Forge: Target-Directed Relational Closure

A concrete, tested research extension to Forge's existing design: discover
coupled polynomial invariants and prove universal behavior of polynomial folds
by target-directed linear-span or polynomial-ideal closure.

Start with `article/forge-relational-closure.pdf` (and its standalone `.tex`).
The article includes the exact fragment, full mathematical arguments, worked
examples, repository-delta analysis, library choices, integration modules,
experimental results, limitations, and reproduction instructions.

## What was executed

- **62 distinct synthetic problems**, each run with both algorithms: 124 runs.
- **Ideal:** 45 independently accepted positive certificates, 17 independently
  accepted concrete counterexamples, no unknowns in this designed corpus.
- **Linear:** 29 accepted positive certificates, 17 accepted counterexamples,
  16 unknowns caused by the generated-polynomial degree cap.
- **108 evidence files** replayed by a separate standard-library checker, using
  `python -S`, without importing search or SymPy. This count includes paired
  outputs for the same problem, not 108 distinct theorems.
- **40 regression tests passed**, including a separate 80-instance scalar
  differential test (not included in the 62-problem corpus count).
- **254 Lean polynomial identity declarations generated** from the 45 positive
  ideal certificates. Generation is not compilation or source-goal proof.

## What was NOT executed

The new Lean files were **not compiled**: no Lean/Lake executable was available.
`results/lean-status.json` records NOT_RUN. There is no installed `forge` tactic,
no verified Lean source extractor, no live Leant/Djex integration, no Lean axiom
audit, and no comparison against `grind`, Aesop, or other tactics. The independent
Python checker is not formally verified. No GitHub repository was modified.

## Quick reproduction

From this directory, with Python 3.10+ (executed here with Python 3.13.5):

```sh
python -m pip install -r requirements.txt
python -m unittest discover -s prototype -p 'test_*.py' -v
python -S prototype/replay_corpus.py
```

Replay one certificate without third-party packages:

```sh
python -S prototype/verify_stdlib.py \
  results/experiment/problems/nonlinear_equivalence_00.json \
  results/experiment/evidence/nonlinear_equivalence_00.ideal.json
```

Solve any problem in the documented JSON format (with a hard process timeout):

```sh
python prototype/solve_problem.py \
  results/experiment/problems/nonlinear_equivalence_00.json \
  --mode ideal --evidence my-checked-evidence.json
```

Reproduce discovery in a NEW output directory:

```sh
python prototype/run_experiments.py --output reproduced-results --jobs 1
```

The default allows four parallel worker processes; choose `--jobs 1` for a
simpler timing experiment. Nonempty outputs are rejected unless `--resume` is
explicit. The recorded run was interrupted and resumed with a different worker
concurrency, so its timing columns must not be used for a speedup claim.

Regenerate Lean identity text with the independent checker:

```sh
python -S prototype/emit_lean.py
```

With Lean and Lake installed, prepare the pinned Mathlib project separately:

```sh
cd lean
lake update
lake exe cache get
cd ..
python prototype/check_lean.py --output reproduced-lean-status.json
```

The last commands are instructions for a future local run, not executed claims.
The Lean runner distinguishes absent tools, timeouts, failures, and elaboration.
It does not audit transitive axioms.

## Package layout

- `article/`: LaTeX and PDF.
- `prototype/search.py`: exact SymPy discovery, linear and ideal modes.
- `prototype/verify_stdlib.py`: separate sparse rational arithmetic and checker.
- `prototype/cases.py`: reproducible corpus, fixed seed and constructions.
- `prototype/test_closure.py`: rejection, boundary, and differential tests.
- `prototype/run_experiments.py`: supervised comparison and evidence recording.
- `prototype/replay_corpus.py`: stdlib-only replay of stored evidence.
- `prototype/emit_lean.py`: polynomial-identity source emission, not compilation.
- `prototype/check_lean.py`: local compilation/status runner.
- `lean/`: authored specimens, generated identities, and pinned project.
- `results/experiment/`: original problems, run records, evidence, CSV, summary.
- `results/`: test/replay/status receipts and separated failed-run diagnostic.
- `docs/`: review scope, semantics, and run-history notes.

## Review pins

- Forge: `674521027d968d59f7b83220ed52304a85cb55e2`
- Leant: `6bf05ad78c467989e68290f2d08bbed40802d485`
- Djex: `e8778f4ebd63e1f9b9b410fa4de8d14a8a04c9e5`
- Leant's separately reported Djex dependency pin: `e237e866`
- Intended Lean baseline: `v4.34.0`
- Intended Mathlib baseline: `1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`

## Semantic boundary

State and input values are rational; all updates are **total simultaneous
polynomials**; control is finite; initial states are polynomially parametrized;
the target is a finite collection of polynomial equalities at observation
locations. Arbitrary guards, division, natural truncation, fixed-width arithmetic,
higher-order opaque callbacks, and unrestricted recursive programs are not
silently translated into this fragment. A source-language proof still needs
certified extraction and Lean replay.

No new mathematical discovery is claimed for ideals, algebraic invariants, or
polynomial-automaton zeroness. The contribution is the specific incremental
algorithm, certificate and witness construction, tested implementation, and
integration design for Forge.
