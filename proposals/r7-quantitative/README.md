# Forge-Q: Certified Quantitative and Relational Proof Search

Prepared for Vladimir Reshetnikov, 2026-09-15.

Start with **article/forgeq.pdf**. The editable LaTeX source is
**article/forgeq.tex**, with two small table inputs generated from the recorded
results. This is a proposed extension of Forge at revision
`c98e47c5f804e92880fc1d0e378c1b95832b685c`, not a replacement for its existing
workers.

## Delivered and not delivered

Six exact-rational Python workers are implemented: maximum MDP reachability;
uniform expected hitting-time bounds; finite optimal transport and Hall
obstructions; strong probabilistic bisimulation and certified deletion traces;
affine coupling/contraction bounds; and symbolic polynomial cost potentials for
stopped skip-free walks. Search, checking, and test oracles are separate.

The recorded corpus contains **520 accepted certificate records** (508 distinct
worker/problem pairs), **520 rejected deliberately invalid mutations**, and five
explicit UNKNOWN controls. All 24 unit-test methods pass in normal and optimized
Python. Independent replay forbids producer, oracle, and scientific-library
imports. See `results/summary.json` for actual outcome kinds, not just totals.

**There is no implemented Lean tactic in this package.** Lean and Lake were
unavailable in the authoring environment. The files under `lean/` are uncompiled
candidate foundations; no certificate was checked by Lean's kernel, no source
reflection was implemented, and no comparison against `grind` or another tactic
was performed. `results/lean-status.json` records NOT_RUN, not success.

## Run the prototypes

Python 3.10 or later is intended; the recorded run used Python 3.13.5. No pip
packages are required. Cross-version runs have not been tested.

```sh
cd prototype
python -S -m unittest discover -s tests -v
python -O -S -m unittest discover -s tests -v
python -S replay.py
python -S run_experiments.py
python -S demo.py
```

The experiment runner defaults to `../reproduced-results`, so it does not
silently overwrite the original receipts. Timings are expected to vary. The
random generator is seeded, and the observed problems/certificates are also
stored explicitly. The replay script needs no generator and admits no UNKNOWN
result as a certificate.

Minimal direct API:

```python
from forgeq import search, checker

problem = {
    "actions": [[["1/2", "1/2"]], [["0", "1"]]],
    "target": [1],
}
certificate = search.runtime(problem)
result = checker.audit("runtime", problem, certificate)
print(certificate)  # potential [2, 0]
print(result)       # scoped uniform expected-hitting-time claim
```

Producers expect well-formed inputs. The checker validates problems independently
and rejects floats, booleans as numbers, malformed laws, duplicate identifiers,
and noncanonical rational strings. This is research code, not a hostile-input
service or a formally verified checker. Read the resource and security limits in
the article before adapting it to an external process boundary.

## Outcome meanings

A Hall certificate refutes coupling in the **supplied relation**. A negative
bisimulation trace refutes **strong bisimulation**, not trace-distribution
equality. A rate obstruction refutes the **named one-step metric/rate/error
bound**, not mixing. A zero-cost potential does not establish termination. An
exit rank for reachability reaches either the target or a closed dead region; it
is not an expected time to success. UNKNOWN never refutes a source proposition.

## Lean candidates

The Lake configuration pins Lean v4.34.0 and the Mathlib revision recorded by
Forge. The candidate files provide only an abstract finite-iteration lemma,
rational finite-prefix bounds, and one marginal expectation identity. Their
exact contents and missing bridges are explained in the article.

With the toolchain and network access available in your own environment:

```sh
cd lean
lake update
lake exe cache get
lake build
cd ..
python tools/check_lean.py --mathlib
```

The harness writes actual status to `reproduced-results/lean-status.json` by
default. The `#print axioms` commands are there to expose dependencies if the
files elaborate; their presence is not a completed axiom audit. Any elaboration
errors must be repaired before these files can be treated as checked code.

## Rebuild the article

A TeX distribution with pdfLaTeX, Latin Modern, AMS packages, listings, hyperref,
xurl, booktabs, and microtype is required.

```sh
python tools/build_article.py
```

Alternatively run `pdflatex -interaction=nonstopmode -halt-on-error forgeq.tex`
three times from `article/`. PDF rendering/layout was inspected during authoring;
editing the source can of course change pagination.

## Evidence and provenance

`docs/source-audit.md` records what was actually inspected. It is not a claim to
have executed all eighteen existing Forge proposals. `docs/capability-ledger.md`
distinguishes tested algorithms from paper theorems and unimplemented bridges.
`docs/benchmark-notes.md` explains the pilot correction, duplicates, outcome
counts, tiny input sizes, oracle limitations, and mutation design.

No third-party repository snapshot, paper, binary toolchain, or font file is
included. The article credits existing probabilistic-verification theory rather
than claiming it as new mathematics. The new code may be used under the MIT
license included in this archive.
