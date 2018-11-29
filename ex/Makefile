SRC=../src
TST=../test

%.pm: %.aln
	$(SRC)/allenc $<

# Building and running the examples

ex: ex.pm
	$(SRC)/allen -s $(TST)/log0.csv $<

monkey: planning/monkey.pm
	cat planning/monkey.log | $(SRC)/allen $<

clean:
	rm -f *.pm planning/*.pm
