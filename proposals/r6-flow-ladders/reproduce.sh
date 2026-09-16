#!/bin/sh
set -eu
cd "$(dirname "$0")/prototype"
PYTHON=${PYTHON:-python3}
"$PYTHON" -S -m unittest discover -s tests -v
"$PYTHON" -S replay.py
"$PYTHON" -S run_experiments.py --out reproduced-results
"$PYTHON" -S replay.py reproduced-results/certificates.json
