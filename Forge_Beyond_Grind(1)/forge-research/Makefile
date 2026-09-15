.PHONY: test experiments replay pdf all clean
all: test replay pdf

test:
	python -m pytest -q

experiments:
	python scripts/run_experiments.py

replay:
	python scripts/verify_artifacts.py

pdf:
	cd article && latexmk -xelatex -interaction=nonstopmode -halt-on-error forge.tex

clean:
	cd article && latexmk -c forge.tex
	find . -type d -name __pycache__ -prune -exec rm -rf {} +
