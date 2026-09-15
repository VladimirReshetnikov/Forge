"""Build the article with pdfLaTeX; temporary compiler files are not packaged."""
from pathlib import Path
import shutil, subprocess, tempfile

root=Path(__file__).resolve().parent
article=root/'article'
exe=shutil.which('pdflatex')
if exe is None:
    raise SystemExit('pdflatex not found. Install a LaTeX distribution with the packages used by the source.')
with tempfile.TemporaryDirectory(prefix='forge-article-') as temp:
    for _ in range(3):
        run=subprocess.run([exe,'-interaction=nonstopmode','-halt-on-error',f'-output-directory={temp}',
                            'forge_extensions.tex'],cwd=article,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        if run.returncode:
            print(run.stdout)
            raise SystemExit('LaTeX build failed; see diagnostics above.')
    shutil.copy2(Path(temp)/'forge_extensions.pdf',article/'forge_extensions.pdf')
    # Retain an external review log, not transient LaTeX aux files.
    (root/'results'/'latex-build.log').write_text(run.stdout)
print(article/'forge_extensions.pdf')
