# Delivery checks

The final article was compiled with pdfLaTeX after cross-reference resolution.
The final compiler transcript is `results/latex-build.txt`; it has no undefined
references, duplicate page anchors, or overfull/underfull box warnings.

All 29 PDF pages were rendered with Poppler. A full-page contact sheet was
visually inspected, and detailed mathematical and results-table pages were
inspected at higher resolution. No clipping or missing mathematical glyphs
was observed. The temporary render images are not included in the archive.

The delivered Python files reran all 27 unit-test methods successfully and
reproduced the exact stored corpus and mutation records. Standalone replay
accepted 650 objects without producer/oracle imports. The ten named models
also passed CLI search and check smoke tests; a deliberate search cutoff
returned unknown with exit status 2. Machine-readable checks are in `results/`.

The Lean specimen remains uncompiled. The package does not claim that visual
inspection, Python replay, or absence of proof placeholders establishes a
Lean theorem.
