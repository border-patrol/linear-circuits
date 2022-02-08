IDRIS2=idris2
HYPERFINE=hyperfine

TARGETDIR = ./build/exec

UPDATE ?= --interactive

THREADS ?= --threads $(shell (nproc || sysctl -n hw.ncpu) 2>/dev/null || echo 1)
OPTS ?=



.PHONY: netlist-testbin netlist

testbin-netlist:
	${IDRIS2} --build netlist-tests.ipkg

test-netlist: netlist-testbin
	${TARGETDIR}/netlist-tests        \
	$(PROG_BIN)    \
	--timing         \
	$(UPDATE) \
	$(THREADS) \
	--only $(ONLY)

.PHONY: idealised-testbin idealised

testbin-idealised:
	${IDRIS2} --build idealised-tests.ipkg

test-idealised: idealised-testbin
	${TARGETDIR}/idealised-tests        \
	$(PROG_BIN)    \
	--timing         \
	$(UPDATE) \
	$(THREADS) \
	--only $(ONLY)


.PHONY: test clean clobber

clean:
	find . -name 'output' | xargs rm -f

clobber: clean
	${RM} -rf build
