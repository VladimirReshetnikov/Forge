#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root/article"
command -v pdflatex >/dev/null || { echo 'pdflatex is required' >&2; exit 2; }
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error forge-noncommutative.tex > "build-pass-$pass.log"
done
printf 'Built %s\n' "$root/article/forge-noncommutative.pdf"
