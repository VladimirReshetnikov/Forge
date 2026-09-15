# Forge: Designing a More Capable Lean Tactic

The main article is `article/forge.pdf`; its editable source is `article/forge.tex`.
Forge is a proposed proof-obligation planner and certificate layer above Lean's
`grind`, not a production tactic implemented by this archive.

## Evidence status

The supplied Python experiment passed **1,680 assertions**, produced **24 saved
certificate bundles**, and independently replayed all of them. Exact arithmetic
and explicit proof traces are used in acceptance. The Python checkers are
hand-written and **not formally verified**.

The Lean-facing files are **uncompiled integration targets**. The included
`results/lean_status.json` records `NOT_RUN` because no Lean/Lake executable was
available in the experiment environment. No empirical comparison against Lean's
`grind`, Aesop, or LeanHammer was performed. The article does not claim otherwise.

## Main contents

| Path | Content |
| --- | --- |
| `article/forge.tex`, `article/forge.pdf` | Detailed design, algorithms, correctness arguments, experiments, references |
| `prototype/polynomial.py` | Exact sparse rational polynomials and independent Bernstein conversions |
| `prototype/quadratic.py` | Exact symmetric-pivot decomposition of nonnegative global quadratics |
| `prototype/cone.py` | Finite-dictionary numerical LP search, exact replay, Lean proof emission |
| `prototype/bernstein.py` | Adaptive box certificates with checked coverage trees |
| `prototype/induction.py` | Tiny typed equational prover with structural-induction replay |
| `prototype/horn.py` | Demand slicing and indexed forward chaining on ground Horn rules |
| `prototype/replay.py` | Standalone saved-certificate checker using only the standard library |
| `prototype/run_all.py` | Deterministic tests and mechanism ablations |
| `results/*.csv`, `results/summary.json` | Recorded measurements, controls, and environment |
| `results/certificates/` | 24 replayable bundles; rational values are strings, never JSON floats |
| `lean/` | Generated arithmetic proofs, induction examples, contract sketch, pinned project |
| `scripts/check_lean.py` | Honest compiler-status runner, independent of Python experiment results |

## Reproduce Python experiments

Use Python 3.10 or newer with compatible wheels for the pinned search libraries.
The recorded run used Python 3.13.5 on Linux x86_64, NumPy 2.3.5, SciPy 1.17.0,
and SymPy 1.14.0. In the package root:

```sh
python -m pip install -r requirements.txt
python prototype/run_all.py
python prototype/replay.py results/certificates/*.json
```

`run_all.py` overwrites the experiment results and generated arithmetic Lean
examples. The seed is 20260914. Numerical solvers, versions, and platform details
can affect timings and which valid cone certificate is returned; acceptance is
always exact. An inability to reconstruct a candidate is an unknown/rejected
search result, not proof of the opposite statement.

Certificate replay does not require NumPy, SciPy, or SymPy. This was also run with
site packages disabled:

```sh
python -S prototype/replay.py results/certificates/*.json
```

On a shell that does not expand wildcards, pass the JSON paths explicitly.

## What the tests say

The ten selected cone goals have 0, 4, and 9 successes under diagonal-square,
pair-square, and hypothesis-product dictionaries. These are deliberately selected
mechanism tests, not an unbiased theorem corpus. The exact quadratic path proves
4 curated and 60 generated examples. The generated examples are constructed from
positive square combinations and thus carry an explicit selection bias.

Adaptive Bernstein proves 8 of 9 true box inequalities, versus 3 without
subdivision; the false control is never certified. The nonnegative polynomial
`(x - 1/3)^2` exposes a real limitation of midpoint-only subdivision, and is
handled by the quadratic representation instead.

Accumulator generalization changes the induction result from 6/8 to 8/8.
Induction subjects are supplied; dependent types and automatic subject selection
are not implemented. The sequence installs only previously checked lemmas.

Demand slicing changes the synthetic Horn result from 3/12 to 12/12 at a
100-firing budget. The examples intentionally put decoys first. Both modes still
pay the full index-construction cost. In 500 additional comparisons, both modes
agree with a naive least-fixed-point computation. This is not a model or timing
benchmark of grind's E-matching.

## Lean example project (not executed here)

The project pins:

- Lean: `leanprover/lean4:v4.34.0`
- Mathlib: `1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`

With Lean/Lake installed, enter `lean/` and fetch the dependencies:

```sh
lake update
lake exe cache get
```

Then return to the archive root and run:

```sh
python scripts/check_lean.py
```

The runner writes `results/lean_status.json`; it reports missing tools, compile
failures, and timeouts instead of inventing a success. Compilation success alone
is not a full transitive-axiom audit and does not demonstrate a gain over grind.
The article explains the stricter evidence policy, including the additional
native-evaluation trust documented for `bv_decide`.

`DesignAPI.lean` contains proposed data contracts only. There is intentionally no
executable `forge` parser or full planner in this package. `ConeExamples.lean` and
`QuadraticExamples.lean` are generated direct proofs, not a Lean implementation
of certificate search. `InductionExamples.lean` provides ordinary proofs of the
cross-engine integration targets, not claims that the proposed planner generated
them.

## Build the article

With XeLaTeX and the STIX, Latin Modern Math, and DejaVu Sans Mono fonts installed:

```sh
cd article
xelatex -interaction=nonstopmode -halt-on-error forge.tex
xelatex -interaction=nonstopmode -halt-on-error forge.tex
```

The source uses standard TeX Live packages. No font files or third-party toolchains
are included. Bibliographic sources and their concrete URLs are in the article;
version-sensitive Lean example dependencies are pinned separately.

## Safety and limitations

The certificate parser includes basic input limits, but the Python programs are
research prototypes, not a hardened service for arbitrary hostile files. Search
failure, unsupported syntax, and rejected evidence are never advertised as
mathematical refutations. Reifying actual Lean expressions, verifying the Python
checker in Lean, fully implementing induction motive selection, and measuring the
complete proposed tactic remain future implementation work.
