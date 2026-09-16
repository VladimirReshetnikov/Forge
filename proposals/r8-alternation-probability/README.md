# Forge beyond Universal Closure

**Alternating strategies, probabilistic couplings, and quantitative liveness**

Start with `article/forge-alternation-probability.pdf`. Complete editable LaTeX
sources and build scripts are beside it. The proposal is relative to Forge
commit `c98e47c5f804e92880fc1d0e378c1b95832b685c`; the reviewed inventory and
source pins are recorded under `docs/`.

## Four implemented Python workers

1. Parity-game solving with positional strategies and threshold-local rank
   certificates for infinite adversarial behavior.
2. Exact optimal relational couplings, with full marginals and a Hall-dual
   witness proving the minimum unavoidable relation failure probability.
3. Greatest alternating probabilistic simulation, with a matching coupling for
   every source action and replayable obstructions for eliminated state pairs.
4. Worst-case expected termination under all schedulers, using exact Bellman
   potentials and tight policies, or a reachable controlled nonterminal trap.

The mathematical subjects are established. The new contribution is this
repository-relative extension, its concrete certificate formats, integration
plan, and tested implementation. Existing Forge induction, polynomial,
witness-synthesis, closure, and planner mechanisms are not re-proposed here.

## Evidence

The full deterministic run has 884 parity problems, 400 transport problems,
180 MDPs, and 100 simulation problems. Every output agreed with a structurally
independent tiny-model oracle. All deliberately invalid mutations were
rejected. Fourteen focused regressions passed. Counts have different units;
there is no pooled Lean theorem success rate.

All stored certificates replay with proposer and oracle imports forbidden and
site packages disabled. The four searches themselves are also standard-library
only. On 211 of the 400 transport inputs, the optimal coupling's defect was
strictly smaller than that of the independent product on the same input.

**No Lean compiler was run, no Lean certificate checker is verified, and no
comparison against `grind` or another tactic was executed.** The files under
`lean/` are explicitly uncompiled, narrowly scoped lowering specimens. The
Python checks do not constitute kernel proofs. The source-to-Lean bridge and
actual `forge` worker integration remain to be implemented.

## Reproduce

Python 3.10+ syntax; recorded environment Python 3.13.5. No packages to install.
From the archive root:

```sh
cd prototype
python -S -m unittest discover -s tests -v
python -S run_experiments.py --output ../reproduced-results/full
python -S replay.py ../results/full/corpus.json
python -S examples.py --output ../reproduced-results/examples
```

Choose a new output path for each experimental run. The harness does not
silently overwrite recorded reports and retains partial output on a failure.
`results/smoke` is a separate earlier workload, not additional full-run data.
`results/examples` contains the article's nine explicit worked examples and a
search-free replay receipt.

## Build the article

Use stock TeX Live or MiKTeX with pdfLaTeX, Latin Modern, and TikZ.

```sh
cd article
bash build.sh
```

On PowerShell, run `./build.ps1`. Alternatively run
`pdflatex -interaction=nonstopmode -halt-on-error forge-alternation-probability.tex`
three times. No shell escape, external bibliography tool, or nonstandard fonts
are required.

## Implementation map

- `prototype/forge_ap/models.py`: normalized exact representations and parser.
- `prototype/forge_ap/search.py`: four proposers.
- `prototype/forge_ap/check.py`: local verification without search algorithms.
- `prototype/tests/oracles.py`: independent finite computations for testing.
- `prototype/tests/test_regressions.py`: semantic rejection controls.
- `prototype/replay.py`: retained-certificate replay with an import barrier.
- `docs/STATUS.md`: implemented / tested / uncompiled / designed-only distinctions.
- `docs/AUDIT.md`: non-duplication scope and limits of the source review.

The parser and worker runtime are research code, not hardened for hostile inputs.
The package does not alter the user's repository. Own-authored material is
MIT-0; no third-party source trees, paper PDFs, or font files are redistributed.
