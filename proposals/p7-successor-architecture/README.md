# Forge: a proof-producing successor architecture for Lean's `grind`

The article is in **`article/forge.pdf`**; editable source is **`article/forge.tex`**.
The design uses Lean **4.34.0** as its inspected baseline (September 14, 2026).

## What is implemented

Four Python components are implemented and executed:

1. Bounded nonnegative-polynomial certificate discovery: a floating LP proposes a support; exact rational reconstruction and a separate identity checker decide acceptance.
2. Integer-lattice witness extraction: unimodular elimination returns a complete affine family or a replayable divisibility obstruction.
3. Generalized accumulator-invariant synthesis: rational coefficient solving establishes universal base and step identities for polynomial increments.
4. Demand-directed finite ground-Horn reasoning: backward relevance closure followed by indexed forward chaining, with separately replayed derivations.

These are component prototypes, **not an installed Lean `forge` tactic**. The article specifies the outer proof planner, scoped evidence broker, Lean adapters, richer certificates, and SAT/SMT integration needed for a production implementation.

## Recorded results

`results/experiments.json` and `results/run.log` record:

- 833 principal component test cases, resulting in 891 accepted certificate checks.
- 330 deliberately corrupted certificates rejected.
- 150 exact polynomial cross-checks against SymPy.
- 897 comparisons of synthesized accumulator formulas with recursive execution.
- Five expected cone-search misses and two expected invariant-template misses.

Cases and checks are different units: some Horn cases compare two successful derivations, while others have no derivation. Timing repetitions and additional archived demonstrations are excluded from the aggregate check count. This is not a Lean benchmark or a collection of 891 independent held-out problems.

`results/certificates/` contains 26 representative certificates: 9 cone identities, 5 lattice traces, 11 accumulator invariants, and 1 Horn derivation. All 26 passed the separate standard-library-only replay in `results/replay.json`.

**Lean execution status:** no `lean`/`lake` executable was available in the authoring environment. The three files under `lean/` contain generated or illustrative ordinary Mathlib proof scripts and are explicitly marked **uncompiled**. `results/lean-status.json` records `not_run`; no kernel-checking or performance comparison with `grind` is claimed.

## Replay certificates without scientific Python packages

From the archive root:

```console
python prototype/verify_artifacts.py
```

This performs exact software checks and does not call SciPy, NumPy, SymPy, a Lean runtime, or any external solver. It is not itself a formally verified checker. The recorded environment used Python 3.13.5.

## Repeat discovery and tests

Use a fresh environment compatible with the pinned scientific packages (Python 3.13 was used here). Install:

```console
python -m pip install -r prototype/requirements.txt
```

POSIX shell:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python prototype/run_experiments.py
python prototype/verify_artifacts.py
python prototype/emit_lean.py
python prototype/make_tables.py
```

PowerShell:

```powershell
$env:OPENBLAS_NUM_THREADS = '1'
$env:OMP_NUM_THREADS = '1'
python .\prototype\run_experiments.py
python .\prototype\verify_artifacts.py
python .\prototype\emit_lean.py
python .\prototype\make_tables.py
```

Do not use Python's `-O` option: the test runner intentionally uses assertions. The runner overwrites `results/experiments.json` and regenerates representative certificates. Save a copy of the supplied results before comparing another machine. Timings are machine-dependent and include the particular work described in the article; they are not interchangeable across components.

The exact checker modules can also be imported directly from `prototype/`. `sos.discover` needs SciPy; the corresponding `check` functions do not. Input and certificate sizes are not hardened against hostile resource-exhaustion attacks.

## Compile the emitted Lean scripts

The scripts require an **existing compatible Mathlib Lake project**. The archive does not install dependencies, modify a project, or claim that arbitrary current dependency branches compile together.

```console
python lean/run_checks.py --project /path/to/mathlib-project --output local-lean-results.json
```

PowerShell example:

```powershell
python .\lean\run_checks.py --project C:\src\YourMathlibProject --output .\local-lean-results.json
```

The harness runs `lake env lean` on each supplied `.lean` file, records compiler output and elapsed time, and reports missing executables, errors, and timeouts. It is a compilation harness, **not a tactic benchmark**. A successful local run is required before describing the generated files as verified Lean proofs.

`GeneratedSOS.lean` uses explicit nonnegativity lemmas and `ring`; `GeneratedInduction.lean` uses ordinary generalized induction and rational arithmetic; `WitnessExamples.lean` uses explicit witnesses and existing arithmetic tactics. No implementation of the proposed `forge` syntax is included.

## Build the article

The article contains its bibliography. Keep the three `table-*.tex` files alongside `forge.tex`.

```console
cd article
xelatex -interaction=nonstopmode -halt-on-error forge.tex
xelatex -interaction=nonstopmode -halt-on-error forge.tex
```

A third pass can be needed after pagination changes. The source prefers Arimo and DejaVu Sans Mono, with TeX-font fallbacks, and uses Latin Modern Math. Standard TeX packages include `fontspec`, `unicode-math`, `booktabs`, `longtable`, `tabularx`, `fvextra`, `titlesec`, `xurl`, and `hyperref`. No font binaries are distributed.

## Source and validation records

`sources.json` lists the consulted primary sources and the available inspected GitHub blob identifiers. These identify observations, not a bundled checkout of Lean or its dependencies. The article distinguishes current `grind` features from proposed additions and notes the deprecated status of `lean-egg` and the native-trust boundary of `bv_decide`.

`results/validation.md` summarizes the artifact checks. The full design includes an equal-budget benchmark protocol, theorem-leakage controls, component ablations, strict/native trust separation, and scope/rollback adversarial tests to perform in the eventual Lean implementation.
