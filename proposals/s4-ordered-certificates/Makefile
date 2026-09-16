.PHONY: test pdf

test:
	python -S prototype/run_tests.py --output reproduced-results
	python -S prototype/run_separation.py --source reproduced-results --output reproduced-separation

pdf:
	cd article && pdflatex -interaction=nonstopmode -halt-on-error forge_ordered.tex
	cd article && pdflatex -interaction=nonstopmode -halt-on-error forge_ordered.tex
	cd article && pdflatex -interaction=nonstopmode -halt-on-error forge_ordered.tex
