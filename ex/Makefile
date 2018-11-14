SRC=../src
TST=../test

%.pm: %.aln
	$(SRC)/allenc $<

# Sample target:
ex: ex.pm
	$(SRC)/allen -s $(TST)/log0.csv $< 

clean:
	rm -f *.pm
