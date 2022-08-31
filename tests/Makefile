# -- [ Makefile ]
#
# Makefile for testing
#
# Copyright : (c) Jan de Muijnck-Hughes
# License   : see ../LICENSE
#
# -- [ EOH ]

# [ Options ]

IDRIS2=idris2
HYPERFINE=hyperfine

TARGETDIR = ./build/exec

UPDATE ?= --interactive

THREADS ?= --threads $(shell (nproc || sysctl -n hw.ncpu) 2>/dev/null || echo 1)
OPTS ?=


# [ Typical Netlist language ]

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

# [ Typical Linear language ]

.PHONY: linear-testbin linear

testbin-linear:
	${IDRIS2} --build linear-tests.ipkg

test-linear: linear-testbin
	${TARGETDIR}/linear-tests        \
	$(PROG_BIN)    \
	--timing         \
	$(UPDATE) \
	$(THREADS) \
	--only $(ONLY)

# [ Idealised Netlist language ]

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

# [ Housekeeping ]

.PHONY: test clean clobber

clean:
	find . -name 'output' | xargs rm -f
	find . -name '*.dot' -or -name '*.png' | xargs rm -f

clobber: clean
	${RM} -rf build


# -- [ EOF ]
