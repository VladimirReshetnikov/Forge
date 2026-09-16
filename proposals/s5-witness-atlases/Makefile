.PHONY: article test
article:
	cd article && latexmk -pdf -interaction=nonstopmode -halt-on-error atlas.tex
test:
	python run_all.py
