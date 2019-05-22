SRC=../src
TESTS=suite-s suite-s-1

all: out/ $(TESTS:%=out/%.diff)

out/:
	mkdir out

suite.pm: suite.aln
	$(SRC)/allenc $<

out/suite-s: suite.pm
	$(SRC)/allen -s log0.csv -D -T suite.pm >$@

out/suite-s-1: suite.pm
	$(SRC)/allen -s log1.csv -D -T suite.pm >$@

out/%.diff: out/%
	diff $< ref/$(<:out/%=%) >$@

out/suite-s-1.diff: out/suite-s-1
	diff $< ref/suite-s >$@

clean:
	rm -f suite.pm
	rm -fr out
