SRC=../src
TST=../test

%.pm: %.aln
	$(SRC)/allenc $<

# Building and running the examples

ex: ex.pm
	$(SRC)/allen -s $(TST)/log0.csv $<

out/holdslib1: holdslib.pm $(TST)/suite.pm
	$(SRC)/allen -s $(TST)/log0.csv -l $^ >$@
out/holdslib0: $(TST)/suite.pm
	$(SRC)/allen -s $(TST)/log0.csv $< >$@
out/holdslib.diff: out/holdslib0 out/holdslib1
	diff $^ >$@

monkey: planning/monkey.pm
	cat planning/monkey.log | $(SRC)/allen $<

clean:
	rm -f *.pm planning/*.pm out/*
