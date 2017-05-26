MODULES := \
	Automation \
	IOA \
	ListOps \
	OptionOps \
	Misc \
	Operators \
	RefinementFacts \
	Simulation \
	Channel \
	CounterSpec \
	CounterRegister \
	Network \
	CounterNetworked \
	KVStore \
	Scratch \
	ThesisExamples \

VS := $(MODULES:%=%.v)
PROJ_NAME := CCDS
COQ_MAKEFILE := coq_makefile

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f $<

Makefile.coq: Makefile $(VS)
	$(COQ_MAKEFILE) -R . $(PROJ_NAME) $(VS) -o $@

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f *.v.d *.vo *.glob
