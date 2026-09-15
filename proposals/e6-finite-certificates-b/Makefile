.PHONY: test replay reproduce article clean
PYTHON ?= python

test:
	$(PYTHON) -m pytest -q

replay:
	$(PYTHON) -S replay.py

reproduce:
	$(PYTHON) run_experiments.py --out reproduced-results

article:
	cd article && pdflatex -interaction=nonstopmode -halt-on-error forge-finite-certificates.tex
	cd article && pdflatex -interaction=nonstopmode -halt-on-error forge-finite-certificates.tex
	cd article && pdflatex -interaction=nonstopmode -halt-on-error forge-finite-certificates.tex

clean:
	$(PYTHON) -c "from pathlib import Path; [p.unlink() for ext in ('aux','log','out','toc') for p in Path('article').glob('*.'+ext)]"
