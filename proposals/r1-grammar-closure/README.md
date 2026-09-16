# Forge Beyond Word Closure

An algorithmic extension prepared against Forge commit
`c98e47c5f804e92880fc1d0e378c1b95832b685c`.

Start with `article/forge_grammar_closure.pdf`. Editable LaTeX and its generated
fixture table are in the same directory. The article describes the source
fragment, complete exact algorithm, certificate soundness, context-free trace
compiler, context quotient, Lean integration plan, and the actual experiments.

## What is implemented

- Many-sorted rational multilinear reachable-span closure, including several
  independently recursive children and explicit grammar restrictions.
- A context-free grammar compiler to matrix-valued summaries.
- A multi-affine source frontend that homogenizes each child slot separately
  and rejects nonlinear use of one child in a monomial.
- Backward one-hole-context closure and exact observable quotient synthesis.
- Independent source interpretation, certificate replay, and compressed
  original-derivation counterexamples.

The mathematical foundation is established multiplicity-tree-automata theory.
The contribution is a specific Forge worker design and tested certificate/source
adapters, not a claim to have invented automata closure or generic tree induction.
The Lean specimen reuses Forge's existing `ForgeClosure.tree_property`.

## What is NOT implemented or established

There is no native `forge` tactic, Lean source reifier, or reflected Lean
certificate checker in this package. No Lean/lake executable was available, so
`lean/ReplayLeafCount.lean` is an **uncompiled, hand-written integration specimen**.
No result here has been checked by Lean's kernel. No performance or solved-goal
comparison against `grind`, Aesop, or another Lean tactic was performed.

Python acceptance is exact executable test evidence, not formal verification of
Python or of the checker. The checker does not import search or compiler code,
but both use Python's standard `Fraction` arithmetic. Input/resource limits are
not a claim of hostile-input hardening. The procedure decides a particular
multilinear equality fragment, not arbitrary recursive programs, CFG language
equivalence, or dependent Church-encoding synthesis.

## Run

Python 3.11+ is the intended minimum; **Python 3.13.5 was actually tested**.
No third-party Python dependencies are required.

```sh
cd prototype
python -S -m unittest -v tests
python -S run_experiments.py
```

Experiments write `reproduced-results/` by default, not the recorded `results/`.

Replay without search:

```sh
python -I -S checker.py \
  ../results/fixtures/balanced_dyck.problem.json \
  ../results/fixtures/balanced_dyck.certificate.json
```

Run the worker on an explicit input problem:

```sh
python -S solve.py input.problem.json --certificate output.certificate.json
python -S solve.py input.problem.json --quotient --certificate quotient.json
```

`solve.py` audits the input source, searches, and replays every returned
certificate. Existing certificate paths are never overwritten. Exit code 0 is a
successfully replayed abstract result (including a counterexample), 3 means
UNKNOWN due to a cutoff, and 2 means input/replay/I/O failure. On UNKNOWN it emits
no new certificate. A quotient certifies observation preservation, not that an
original zero target is true. A plain enclosure likewise makes no target claim.

## Recorded evidence

`results/summary.json` is the machine-readable summary:

| Evidence family | Recorded outcome |
| --- | --- |
| Named fixture certificates | 8 accepted; all 8 also replayed in isolated processes containing only the checker |
| Exhaustive finite-language differential cases | 240/240 agree: 120 PROVED, 120 REFUTED |
| Exact quotient cases | 40/40 certificates accepted; exhaustive matching-derivation observations also agree |
| Deliberately invalid objects | 20/20 rejected |
| Resource-cutoff cases | 3/3 return UNKNOWN without a certificate |
| unittest methods | 18 passed; zero errors/failures |

These are different, overlapping units. **Do not add them into one success count.**
The generated test cases are correctness fixtures, not a representative theorem
corpus. The 40 quotient comparisons include 1,180 observed state pairs. Timings
are incidental single-run measurements, not performance benchmarks.

Notable fixtures:

* `tree_identity`: five finite identities imply the count relation for every
  full binary tree, over an infinite rational summary carrier.
* `balanced_dyck`: three closure identities prove the zero observation on every
  balanced trace; removing the language restriction yields a counterexample.
* `exponential_60`: a 61-node DAG denotes the unique counterexample word of
  length 2^60, with expanded derivation size 2^61 - 1.
* `noisy_tree_quotient`: ambient dimension 5, reachable dimension 4, observable
  dimension 2, with exact preservation diagrams.

## Layout

```
article/       PDF, editable LaTeX, generated fixture table
prototype/     search, source compilers, independent checker, tests, CLI
results/       recorded original inputs, certificates, test logs, environment
lean/          one uncompiled hand-written replay specimen
docs/          scope/novelty ledger, source pins, Lean status, run history
```

## Build the article

```sh
cd article
pdflatex -interaction=nonstopmode -halt-on-error forge_grammar_closure.tex
pdflatex -interaction=nonstopmode -halt-on-error forge_grammar_closure.tex
```

A standard TeX Live installation with Latin Modern, AMS, listings, booktabs,
longtable, enumitem, geometry, xcolor, fancyhdr, microtype, and hyperref suffices.
No shell escape, bibliography processor, or separately distributed font files
are required.
