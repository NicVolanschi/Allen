SRC=../src
TESTS=suite-s-Apt1

all: $(TESTS:%=out/%.diff)

suite.pm: suite.aln
	$(SRC)/allenc $<

out/suite-s-Apt1: suite.pm
	$(SRC)/allen -s log0.csv -D suite.pm >$@

out/%.diff: out/%
	diff $< ref/$(<:out/%=%) >$@

clean:
	rm -f suite.pm out/*
