"""Build the article with pdfLaTeX; runs on Windows or Unix with pdflatex in PATH."""
from pathlib import Path
import shutil,subprocess,sys

def main() -> int:
    compiler=shutil.which('pdflatex')
    if not compiler:
        print('pdflatex is not in PATH. Install a TeX distribution with the packages in the article preamble.',file=sys.stderr)
        return 1
    root=Path(__file__).resolve().parent
    try:
        for _ in range(3):
            subprocess.run([compiler,'-interaction=nonstopmode','-halt-on-error',
                            'forge-infinite-state.tex'],cwd=root/'article',check=True)
    except subprocess.CalledProcessError as exc:
        print(f'LaTeX build failed; see article/forge-infinite-state.log (exit {exc.returncode}).',file=sys.stderr)
        return exc.returncode
    print(root/'article/forge-infinite-state.pdf')
    return 0

if __name__=='__main__':raise SystemExit(main())
