.PHONY: test replay experiment emit-lean pdf

test:
	python -m pytest -q

replay:
	python -S replay.py

experiment:
	python -m forge_delta.experiment --output reproduced-results --repeats 3

emit-lean:
	python emit_lean.py

pdf:
	cd article && pdflatex -interaction=nonstopmode -halt-on-error forge_delta.tex
	cd article && pdflatex -interaction=nonstopmode -halt-on-error forge_delta.tex
