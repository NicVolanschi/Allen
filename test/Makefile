SRC=../src
TESTS=suite-s

all: out/ $(TESTS:%=out/%.diff)

out/:
	mkdir out

suite.pm: suite.aln
	$(SRC)/allenc $<

out/suite-s: suite.pm
	$(SRC)/allen -s log0.csv -D suite.pm >$@

out/%.diff: out/%
	diff $< ref/$(<:out/%=%) >$@

clean:
	rm -f suite.pm
	rm -fr out
