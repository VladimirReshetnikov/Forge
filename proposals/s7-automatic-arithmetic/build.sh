#!/bin/sh
set -eu
cd "$(dirname "$0")/article"
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error forge-automatic-arithmetic.tex
done
