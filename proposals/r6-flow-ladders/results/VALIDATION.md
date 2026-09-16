# Final validation

## Reproduction

The complete `./reproduce.sh` command succeeded in the authoring environment
(Python 3.13.5). Its console output is `results/reproduction.log`; the new-run
summary is `results/reproduction-summary.json`.

- All 22 unittest methods passed.
- All 304 stored records replayed without site packages or discovery modules.
- Fresh generation reproduced the lane counts 196 / 40 / 44 / 8 / 16.
- All 624 targeted invalid mutations were rejected again.
- Every freshly generated certificate and every non-timing record field agreed
  exactly with the accepted corpus. Timings are observations, not stable output.
- The fresh corpus replayed successfully. Its duplicate certificate file was
  removed from the distributable so the default reproduction output directory
  is available on first run.

The optional oracle results are in `results/oracle-results.json`: 200 finite
exhaustive-permutation cases, 200 breadth-first minimum-length comparisons,
200 symbolic derivatives (SymPy 1.14.0), and 161 Decimal enclosure sanity checks.

## Article

The final PDF contains 32 physical pages. It was built with pdfLaTeX, with no
undefined references, unresolved citation markers, overfull boxes, or LaTeX
warnings in the final log. All pages were rendered for layout inspection;
the cover, optimality theorem/pseudocode, worked hyperbolic table, results tables,
and bibliography were inspected at enlarged resolution. Source listings were
kept together and the bibliography fits on its final page.

## Distribution

The ZIP is tested for decompression integrity and its extracted prototype is
replayed with `python -S`. Build intermediates, bytecode caches, duplicate
reproduction files, external repositories, and font files are not distributed.
The LaTeX source, all original prototype modules, recorded evidence, and the PDF
are included.

## Boundaries

Lean compilation: NOT_RUN. Forge integration: DESIGNED, NOT IMPLEMENTED.
Comparison with `grind` or any Lean tactic: NOT_RUN.
The Python checker is not formally verified. Scalar algebra replay follows a
separate sparse path; the numerical proposer and replay share an interval kernel.
A checked grammar obstruction is not a theorem refutation.
