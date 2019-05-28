SRC=../src
TESTS=suite-s suite-s-1 rvlib

all: out/ $(TESTS:%=out/%.diff)

out/:
	mkdir out

suite.pm: suite.aln
	$(SRC)/allenc $<

rvlib.pm: $(SRC)/rvlib.aln
	$(SRC)/allenc -o $@ $<

out/suite-s: suite.pm
	$(SRC)/allen -s log0.csv -D -T suite.pm >$@

out/suite-s-1: suite.pm
	$(SRC)/allen -s log1.csv -D -T suite.pm >$@

out/%.diff: out/%
	diff $< ref/$(<:out/%=%) >$@

out/suite-s-1.diff: out/suite-s-1
	diff $< ref/suite-s >$@

out/suite: suite.pm
	$(SRC)/allen -s log0.csv $< >$@

out/rvlib: rvlib.pm suite.pm
	$(SRC)/allen -s log0.csv -l $^ >$@

out/rvlib.diff: out/suite out/rvlib
	diff $^ >$@

clean:
	rm -f *.pm
	rm -fr out
