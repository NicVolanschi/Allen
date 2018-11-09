SRC=../src
TST=../test

%.pm: %.aln
	$(SRC)/allenc $<

# Sample target:
ex: ex.pm
	$(SRC)/allen -s $< $(TST)/log0.json

clean:
	rm -f *.pm
