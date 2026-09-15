#!/usr/bin/env python3
"""Build the article with three pdfLaTeX passes, without shell escape."""
from pathlib import Path
import shutil
import subprocess
import sys

def main():
    engine=shutil.which('pdflatex')
    if not engine:
        raise SystemExit('pdfLaTeX not found. Install a TeX distribution and add it to PATH.')
    article=Path(__file__).resolve().parent/'article'
    for _ in range(3):
        r=subprocess.run([engine,'-interaction=nonstopmode','-halt-on-error','forge_closure.tex'],cwd=article)
        if r.returncode:
            raise SystemExit('LaTeX failed; inspect article/forge_closure.log.')
    print(article/'forge_closure.pdf')

if __name__=='__main__': main()
