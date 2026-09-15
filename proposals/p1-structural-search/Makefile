PYTHON ?= python3

.PHONY: test verify experiments lean-candidates pdf clean

test:
	cd prototype && $(PYTHON) -m pytest -q

verify:
	cd prototype && $(PYTHON) -S verify_certificates.py

experiments:
	cd prototype && $(PYTHON) run_experiments.py

lean-candidates:
	cd prototype && $(PYTHON) emit_lean.py

pdf:
	cd article && latexmk -pdf -interaction=nonstopmode -halt-on-error forge.tex

clean:
	cd article && latexmk -c forge.tex
