#

all: equiv_holds.vo equiv_until.vo

clean:
	rm -f *.vo *.glob .*.aux

basics.vo: basics.v
	coqc basics.v

enat.vo: basics.vo enat.v
	coqc enat.v

allen.vo: enat.vo allen.v
	coqc allen.v

signal.vo: allen.vo signal.v
	coqc signal.v

compare.vo: signal.vo compare.v
	coqc compare.v

include.vo: compare.vo include.v
	coqc include.v

borders.vo: signal.vo include.vo borders.v
	coqc borders.v

reactives.vo: signal.vo borders.vo reactives.v
	coqc reactives.v

extend.vo: reactives.vo extend.v
	coqc extend.v

allenfuns.vo: extend.vo reactives.vo allenfuns.v
	coqc allenfuns.v

equiv_holds.vo: allenfuns.vo equiv_holds.v
	coqc equiv_holds.v

equiv_until.vo: allenfuns.vo equiv_until.v
	coqc equiv_until.v
