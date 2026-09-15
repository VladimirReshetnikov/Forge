#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
python "$ROOT/scripts/make_tables.py"
cd "$ROOT/article"
lualatex -interaction=nonstopmode -halt-on-error forge.tex
lualatex -interaction=nonstopmode -halt-on-error forge.tex
lualatex -interaction=nonstopmode -halt-on-error forge.tex
