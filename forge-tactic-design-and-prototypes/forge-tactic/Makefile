.PHONY: test experiments pdf clean

test:
	cd prototype && python -m pytest -q

experiments:
	cd prototype && OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python experiments.py

pdf:
	cd article && pdflatex -interaction=nonstopmode -halt-on-error forge.tex
	cd article && pdflatex -interaction=nonstopmode -halt-on-error forge.tex

clean:
	rm -f article/*.aux article/*.log article/*.out article/*.toc
	find prototype -type d \( -name '__pycache__' -o -name '.pytest_cache' \) -prune -exec rm -rf {} +
