SRC=../src
TESTS=suite-s-Apt1

all: $(TESTS:%=out/%.diff)

suite.pm: suite.aln
	$(SRC)/allenc $< >$@

out/suite-s-Apt1: suite.pm
	$(SRC)/allen -s -f10000 -d suite.pm log0.json >$@

out/%.diff: out/%
	diff $< ref/$(<:out/%=%) | \
	  egrep -v '^[<>] (form:|domain:|codomain:|comp:|expr:|iexpr:) ' >$@

clean:
	rm suite.pm out/*
