TARGET=paper
all: pdf

paper.pdf: $(wildcard *.tex) $(wildcard *.bib)
	- pdflatex -shell-escape main
	- bibtex main
	- pdflatex -shell-escape main
	pdflatex -shell-escape main

pdf: paper.pdf

clean:
	rm -f *.eps
	rm -f *.aux *.log *.out *.bbl *.blg *~ *.bak $(TARGET).ps $(TARGET).pdf
	rm *.brf *.lof *.lot *.toc

# End
