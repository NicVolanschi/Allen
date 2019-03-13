SRC=../src
TST=../test
AMIQOPTS=-b '/^tv_salon_real_status$$/=ON/OFF,/^C\d+$$/=OPEN/CLOSED' \
	-q '/^Eau_.*_Instantanee$$/>=0.01,/^Intensite_/>=1,/^bed_pressure$$/>=300'
TAREAALOPTS=-q '/^week_activity$$/>=80,/^day_steps$$/>=5000,/^breath$$/>=10,/^heart$$/>=50'

%.pm: %.aln
	$(SRC)/allenc $<

# Building and running the examples

ex: ex.pm
	$(SRC)/allen -s $(TST)/log0.csv $<

out/suite: $(TST)/suite.pm
	$(SRC)/allen -s $(TST)/log0.csv $< >$@
out/holdslib: holdslib.pm $(TST)/suite.pm
	$(SRC)/allen -s $(TST)/log0.csv -l $^ >$@
out/holdslib.diff: out/suite out/holdslib
	diff $^ >$@

regular: regular.pm
	cat /dev/null | $(SRC)/allen $<

monkey: planning/monkey.pm
	cat planning/monkey.log | $(SRC)/allen $<

packages: video/packages.pm
	cat video/packages.log | $(SRC)/allen $<

amiqual: smarthome/amiqual.pm
	cat smarthome/July_All_Change.log | $(SRC)/allen $(AMIQOPTS) $<

tare-aal: smarthome/tare-aal.pm
	cat smarthome/tare-aal.log | $(SRC)/allen $(TAREAALOPTS) $<

tltl3: verification/tltl3.pm
	cat verification/tltl3.log | $(SRC)/allen $<

clean:
	rm -f *.pm out/* planning/*.pm video/*.pm smarthome/*.pm verification/*.pm
