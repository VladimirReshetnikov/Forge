#!/usr/bin/env python3
"""Build the article with stock pdfLaTeX; no shell or external bibliography tool."""
from pathlib import Path
import shutil
import subprocess
import sys

def main() -> int:
    engine=shutil.which('pdflatex')
    if engine is None:
        print('pdflatex was not found. Install a TeX Live or MiKTeX distribution.',file=sys.stderr)
        return 2
    root=Path(__file__).resolve().parents[1]
    article=root/'article'
    for _ in range(3):
        result=subprocess.run([engine,'-interaction=nonstopmode','-halt-on-error',
                               'forge-infinite-horizon.tex'],cwd=article,check=False)
        if result.returncode:
            return result.returncode
    print(article/'forge-infinite-horizon.pdf')
    return 0

if __name__=='__main__':
    raise SystemExit(main())
