# Run history

## Initial diagnostic failure

The first experiment run ended with `AssertionError: budget did not trigger`; its traceback is preserved in `results/history/attempt1.log`. The one-node-budget fixture used a single atomic formula, which legitimately needs only one node. The fixture was corrected to a negated atom, which needs more than one. This was a test-contract error, not an arithmetic soundness failure. Earlier results from that interrupted execution were not reported as a complete successful suite.

## Run 1

The corrected full suite completed with the summary in `results/run1/summary.json`. Its separate-process replay receipt is `results/replay-receipt.json`. Article measurements and the ablation table refer to this run.

## Interface review

Source review identified that `least_graph` should explicitly reject a proposed fresh name already free in its input relation, not merely output-name equality and binder capture. The helper now collects free variables and rejects that collision. Seven focused interface tests pass; see `results/interface-tests.txt`. The preexisting valid fixtures do not use such collisions.

## Run 2

The full suite was rerun after the interface improvement, preserving its query and certificate corpus separately in `results/run2/`. Its summary equals run 1's summary, including every count and the environment fields. Timings are new measurements and are not assumed equal. Fresh search-free replay accepted all stored objects; see `results/replay-run2.json`.

Runs 1 and 2 use the same seed, generators and mathematical cases. Their counts must not be summed or represented as independent coverage. Neither run invokes Lean or a competing tactic.

## Article build

The article was compiled with pdfLaTeX, with cross-references resolved, and rendered for visual inspection. Intermediate typesetting passes exposed long-code line breaks; the final source uses breakable inline code. Typesetting diagnostics are not included as experiment outcomes.
