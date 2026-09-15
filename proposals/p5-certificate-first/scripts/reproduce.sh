#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../prototype"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
python -m pytest -q
python run_benchmarks.py --output ../results
python validate_artifacts.py --results ../results
python export_lean.py --results ../results --output ../lean
