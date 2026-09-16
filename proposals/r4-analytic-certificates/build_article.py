#!/usr/bin/env python3
"""Build the article with three pdfLaTeX passes; retain a diagnostic build log."""
from pathlib import Path
import shutil
import subprocess
import sys


def main() -> int:
    executable = shutil.which('pdflatex')
    if executable is None:
        print('pdflatex was not found. Install TeX Live or MiKTeX with the packages listed in the article preamble.', file=sys.stderr)
        return 2
    root = Path(__file__).resolve().parent
    article = root / 'article'
    log = article / 'build.log'
    with log.open('w', encoding='utf-8') as out:
        for run in range(1, 4):
            out.write(f'\n=== pdfLaTeX pass {run} ===\n')
            out.flush()
            result = subprocess.run([executable, '-interaction=nonstopmode',
                                     '-halt-on-error', 'forge-analytic-certificates.tex'],
                                    cwd=article, stdout=out, stderr=subprocess.STDOUT)
            if result.returncode:
                print(f'Build failed; see {log}', file=sys.stderr)
                return result.returncode
    print(article / 'forge-analytic-certificates.pdf')
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
