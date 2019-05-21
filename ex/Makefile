SRC=../src
TST=../test
AMIQOPTS=-b '/^tv_salon_real_status$$/=ON/OFF,/^C\d+$$/=OPEN/CLOSED' \
	-q '/^Eau_.*_Instantanee$$/>=0.01,/^Intensite_/>=1,/^bed_pressure$$/>=300'
TAREAALOPTS=-q '/^week_activity$$/>=80,/^day_steps$$/>=5000,/^breath$$/>=10,/^heart$$/>=50'
ORANGE=smarthome/orange
OPTQ_ORG=-q'/^toilet$$/>=0.0001,/bathroom_shower_(hot|cold)water/>=0.0001,/bedroom_bed_pressure/>=200,\
	/bedroom_luminosity/>=20,/office_deskplug/>=1,/kitchen_(cooktop|oven)/>=0.0001,\
	/kitchen_dishwasher/>=0.0001,/(bathroom|kitchen)_sink_(cold|hot)water/>=0.000001,\
	/(entrance|office|toilet)_light/>=1'\
	-b'/bedroom_closet_door/=ON/OFF,/bedroom_drawer/=OPEN/CLOSED,\
	/office_tv/=ON/OFF,/kitchen_presence/=ON/OFF,/kitchen_fridge_door/=OPEN/CLOSED,\
	/kitchen_c[12345]/=OPEN/CLOSED,/livingroom_tv/=ON/OFF,/livingroom_couch/=ON/OFF,\
	/livingroom_table/=ON/OFF, /(entrance|office|toilet)_switch/=ON/OFF'
ALLENRV=$(SRC)/allen -l rvlib.pm

%.pm: %.aln
	$(SRC)/allenc $<

default: ex

out/:
	mkdir out

rvlib.pm: $(SRC)/rvlib.aln
	$(SRC)/allenc -o $@ $<

$(ORANGE)/%.log:
	grep '$(@:$(ORANGE)/%.log=%)' $(ORANGE)/orange4home.log >$@

$(ORANGE)/annotations.log: $(ORANGE)/annotations.csv
	$(ORANGE)/annpp.pl <$< >$@

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

orange: $(ORANGE)/2017-01-31.log $(ORANGE)/2017-01-30.log \
		$(ORANGE)/annotations.log out/
	eval time make out/orange-adl-nap
	eval time make out/orange-switch
	eval time make out/orange-adl-only
	eval time make out/orange-adl-house
	eval time make out/orange-adl-inc
	eval time make out/orange-adl-all
	eval time make out/orange-adl-all-defs
	make out/orange-precision
	make out/orange-reactivity

out/orange-adl-all: $(ORANGE)/adl-all.pm $(ORANGE)/2017-01-31.log rvlib.pm
	$(ALLENRV) $(OPTQ_ORG) <$(ORANGE)/2017-01-31.log $< >$@

out/orange-adl-all-defs: $(ORANGE)/adl-all-defs.pm $(ORANGE)/2017-01-31.log rvlib.pm
	$(ALLENRV) $(OPTQ_ORG) <$(ORANGE)/2017-01-31.log $< >$@

out/orange-adl-inc: $(ORANGE)/adl-inc.pm $(ORANGE)/2017-01-31.log rvlib.pm
	$(ALLENRV) $(OPTQ_ORG) <$(ORANGE)/2017-01-31.log $< >$@

out/orange-adl-house: $(ORANGE)/adl-house.pm $(ORANGE)/2017-01-31.log rvlib.pm
	$(ALLENRV) $(OPTQ_ORG) <$(ORANGE)/2017-01-31.log $< >$@

out/orange-adl-only: $(ORANGE)/adl-only.pm $(ORANGE)/2017-01-31.log rvlib.pm
	$(ALLENRV) $(OPTQ_ORG) <$(ORANGE)/2017-01-31.log $< >$@

out/orange-switch: $(ORANGE)/switch.pm $(ORANGE)/2017-01-30.log rvlib.pm
	$(ALLENRV) $(OPTQ_ORG) <$(ORANGE)/2017-01-30.log $< >$@

out/orange-adl-nap: $(ORANGE)/adl-nap.pm $(ORANGE)/2017-01-31.log rvlib.pm
	$(SRC)/allen $(OPTQ_ORG) <$(ORANGE)/2017-01-31.log $< >$@

out/orange-intervals: $(ORANGE)/intervals.pm out/orange-adl-all $(ORANGE)/annotations.log
	grep -h '^2017-01-31T' out/orange-adl-all $(ORANGE)/annotations.log |\
		sort | $(SRC)/allen -b'/[|]/=START/STOP' $< >$@

out/orange-precision: out/orange-intervals
	$(ORANGE)/precision.pl $< >$@

out/orange-reactivity: $(ORANGE)/adl-all.pm $(ORANGE)/2017-01-31.log rvlib.pm
	$(ALLENRV) $(OPTQ_ORG) -S <$(ORANGE)/2017-01-31.log $< >$@

tltl3: verification/tltl3.pm
	cat verification/tltl3.log | $(SRC)/allen $<

clean:
	rm -f *.pm out/* planning/*.pm video/*.pm smarthome/*.pm verification/*.pm \
		$(ORANGE)/*.pm $(ORANGE)/2017-*-*.log $(ORANGE)/annotations.log
