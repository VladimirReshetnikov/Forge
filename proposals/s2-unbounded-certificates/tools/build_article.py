#!/usr/bin/env python3
"""Portable pdfLaTeX build; no shell escape or bibliography tool required."""
from pathlib import Path
import shutil, subprocess, sys

root=Path(__file__).resolve().parents[1]
engine=shutil.which('pdflatex')
if engine is None:
    raise SystemExit('pdflatex was not found on PATH; install TeX Live or MiKTeX first.')
article=root/'article'
for pass_number in range(1,4):
    result=subprocess.run([engine,'-interaction=nonstopmode','-halt-on-error',
                           'forge-unbounded.tex'],cwd=article,text=True,
                          stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
log=(article/'forge-unbounded.log').read_text(errors='replace')
problems=[line for line in log.splitlines()
          if 'Overfull' in line or 'undefined references' in line or 'undefined citations' in line]
if problems:
    print('\n'.join(problems))
    raise SystemExit('Build produced layout/reference warnings; inspect the log.')
print(article/'forge-unbounded.pdf')
