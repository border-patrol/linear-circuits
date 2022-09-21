#
# Copyright : see COPYRIGHT
# License   : see LICENSE

# [ Options ]

IDRIS2=idris2
HYPERFINE=hyperfine

TARGETDIR = ${CURDIR}/build/exec

bopts ?=

# [ Build the Core Gubbins ]

# .PHONY: circuits
#
# circuits:
#	$(IDRIS2) --build circuits.ipkg


# [ Typical Netlist language ]

.PHONY: netlist netlist-test-bin netlist-test-run netlist-test-update

netlist:
	$(IDRIS2) --build netlist.ipkg


netlist-test-bin:
	${MAKE} -C tests testbin-netlist IDRIS2=$(IDRIS2)

netlist-test-update: netlist-test-bin
	${MAKE} -C tests test-netlist \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGETDIR)/netlist \
			 UPDATE=--interactive \
			 THREADS='' \
			 ONLY=$(ONLY)

netlist-test-run: netlist-test-bin
	${MAKE} -C tests test-netlist \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGETDIR)/netlist \
			 UPDATE='' \
			 ONLY=$(ONLY)

# [ Linear Netlist language ]

.PHONY: linear linear-test-bin linear-test-update linear-test-fast

linear:
	$(IDRIS2) --build linear.ipkg


linear-test-bin:
	${MAKE} -C tests testbin-linear IDRIS2=$(IDRIS2)

linear-test-update: linear-test-bin
	${MAKE} -C tests test-linear \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGETDIR)/netlistL \
			 UPDATE=--interactive \
			 THREADS='' \
			 ONLY=$(ONLY)

linear-test-run: linear-test-bin
	${MAKE} -C tests test-linear \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGETDIR)/netlistL \
			 UPDATE='' \
			 ONLY=$(ONLY)

# [ Idealised Netlist language ]

.PHONY: idealised idealised-test-bin idealised-test-update idealised-test-fast

idealised:
	$(IDRIS2) --build idealised.ipkg


idealised-test-bin:
	${MAKE} -C tests testbin-idealised IDRIS2=$(IDRIS2)

idealised-test-update: idealised-test-bin
	${MAKE} -C tests test-idealised \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGETDIR)/idealised \
			 UPDATE=--interactive \
			 THREADS='' \
			 ONLY=$(ONLY)

idealised-test-run: idealised-test-bin
	${MAKE} -C tests test-idealised \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGETDIR)/idealised \
			 UPDATE='' \
			 ONLY=$(ONLY)

# [ Housekeeping ]

.PHONY: clobber clean

clean:
#	$(IDRIS2) --clean circuits.ipkg
	${MAKE} -C tests clean

clobber: clean
	$(IDRIS2) --clean idealised.ipkg
	$(IDRIS2) --clean netlist.ipkg
	${MAKE} -C tests clobber
	${RM} -rf build/

# -- [ EOF ]
