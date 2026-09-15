.PHONY: test replay pdf clean
PYTHON ?= python3

test:
	OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 $(PYTHON) prototype/run_tests.py --out reproduced-results
	$(PYTHON) -S prototype/replay_certificates.py --results reproduced-results

replay:
	$(PYTHON) -S prototype/replay_certificates.py --results results

pdf:
	cd article && latexmk -pdf -interaction=nonstopmode -halt-on-error forge.tex

clean:
	cd article && latexmk -c
