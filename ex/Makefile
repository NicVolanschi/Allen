SRC=../src
TST=../test
AMIQOPTS=-b '/^tv_salon_real_status$$/=ON/OFF,/^C\d+$$/=OPEN/CLOSED' \
	-q '/^Eau_.*_Instantanee$$/>=0.01,/^Intensite_/>=1,/^bed_pressure$$/>=300'

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

packages: video/packages.pm
	cat video/packages.log | $(SRC)/allen $<

amiqual: smarthome/amiqual.pm
	cat smarthome/July_All_Change.log | $(SRC)/allen $(AMIQOPTS) $<

clean:
	rm -f *.pm out/* planning/*.pm video/*.pm smarthome/*.pm
