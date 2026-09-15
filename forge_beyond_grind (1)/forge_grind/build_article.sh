#!/bin/sh
# Run from any directory; requires XeLaTeX and the fonts named in forge.tex.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$ROOT/article"
for pass in 1 2 3; do
    xelatex -interaction=nonstopmode -halt-on-error forge.tex
done
printf '\nArticle built: %s/article/forge.pdf\n' "$ROOT"
