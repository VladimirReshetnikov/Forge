# Artifact validation — September 14, 2026

## Executed prototype checks

The recorded discovery/test run is in `experiments.json`. It reports 833 principal component cases, 891 accepted certificate checks, 330 deliberately corrupted certificates rejected, 150 exact polynomial cross-checks against SymPy, and 897 secondary accumulator-execution cross-checks. Counts have different units; details and exclusions are in the article and README. Five cone-search misses and two invariant-template misses are expected outcomes, not incorrect proofs.

A separate replay of all 26 archived certificates succeeded. In addition to the ordinary replay command, the final validation ran:

```console
python -S prototype/verify_artifacts.py
python -m compileall -q prototype lean
```

The `-S` run disables automatic site-package initialization. All 26 exact certificate checks still succeeded, using only the Python standard library. Python source compilation succeeded. Neither operation is a formal verification of the checker or a Lean kernel check.

## Lean status

`lean-status.json` records `not_run`: `lake` was not available on PATH in the authoring environment. The three `.lean` files are uncompiled generated or illustrative replay scripts. The supplied harness is a compilation harness, not a benchmark. No executed Lean tactic named `forge`, kernel validation of the emitted files, or measured superiority over `grind` is claimed.

## Article rendering

The final article was compiled with XeLaTeX in three passes and contains 38 pages. The last compilation reported no overfull boxes, missing characters, undefined control sequences, or undefined references. Some underfull-box notices remain; these do not indicate clipped content.

All 38 pages were rendered to PNG with `pdftoppm`. All four contact sheets were visually reviewed for layout, clipping, and pagination. Full-size rendered pages were also inspected, including the unimodular-elimination equations on page 13 and experimental tables on page 29. An automated text-bounding-box check found no text outside the checked safe page region on any page. Rendered inspection images and TeX build intermediates are not included in the archive.

## Packaging

The archive includes the PDF, its editable TeX source and three generated table inputs, original Python prototype and replay code, three uncompiled Lean replay files and their compilation harness, the source record, 26 saved certificates, experiment/replay/status records, README, and original-code license. Font binaries, Python caches, and TeX build intermediates are excluded. The ZIP was reopened and its member CRCs verified after creation.
