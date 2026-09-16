#!/usr/bin/env python3
"""Build the supplied LaTeX article without leaving TeX scratch files beside it."""
from pathlib import Path
import shutil, subprocess, tempfile
root=Path(__file__).resolve().parents[1]
engine=shutil.which('pdflatex')
if engine is None:raise SystemExit('pdflatex is required; article/forgeq.pdf is already supplied.')
with tempfile.TemporaryDirectory(prefix='forgeq-tex-') as directory:
    work=Path(directory)
    for path in (root/'article').glob('*.tex'):shutil.copy2(path,work/path.name)
    for _ in range(3):
        run=subprocess.run([engine,'-interaction=nonstopmode','-halt-on-error','forgeq.tex'],
                           cwd=work,capture_output=True,text=True,timeout=90)
        if run.returncode:
            print(run.stdout)
            raise SystemExit(run.returncode)
    shutil.copy2(work/'forgeq.pdf',root/'article'/'forgeq.pdf')
print(root/'article'/'forgeq.pdf')
