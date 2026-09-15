#!/usr/bin/env python3
"""Build the article using an installed pdfLaTeX (no Python dependencies)."""
from pathlib import Path
import shutil
import subprocess
import sys


def main() -> int:
    engine = shutil.which("pdflatex")
    if engine is None:
        print("pdflatex was not found. Install a TeX distribution and add it to PATH.",
              file=sys.stderr)
        return 2
    article = Path(__file__).resolve().parent / "article"
    for run in range(1, 4):
        print(f"pdfLaTeX pass {run}/3", flush=True)
        result = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
            cwd=article, check=False,
        )
        if result.returncode:
            print(f"Build failed; inspect {article / 'main.log'}", file=sys.stderr)
            return result.returncode
    target = article / "forge-extensions.pdf"
    shutil.copyfile(article / "main.pdf", target)
    print(f"Built {target}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
