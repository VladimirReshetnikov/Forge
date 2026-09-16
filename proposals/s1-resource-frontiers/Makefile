PYTHON ?= python3
.PHONY: article test replay reproduce clean
article:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
test:
	$(PYTHON) -m unittest discover -s prototype/tests -v
replay:
	$(PYTHON) -S prototype/replay.py results/frontiers.jsonl results/accelerated-frontiers.jsonl results/thresholds.jsonl results/parameters.jsonl results/runs.jsonl results/lassos.jsonl results/equivalences.jsonl
reproduce:
	$(PYTHON) -S prototype/experiments.py --out reproduced-results
	$(PYTHON) -S prototype/equivalence_experiments.py --out reproduced-results
	$(PYTHON) -S prototype/acceleration_experiments.py --out reproduced-results
	$(PYTHON) -S prototype/replay.py reproduced-results/frontiers.jsonl reproduced-results/accelerated-frontiers.jsonl reproduced-results/thresholds.jsonl reproduced-results/parameters.jsonl reproduced-results/runs.jsonl reproduced-results/lassos.jsonl reproduced-results/equivalences.jsonl
clean:
	rm -f article.aux article.log article.out article.toc
