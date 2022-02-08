IDRIS2=idris2
HYPERFINE=hyperfine

TARGETDIR = ${CURDIR}/build/exec

bopts ?=

.PHONY: all

circuits:
	$(IDRIS2) --build circuits.ipkg

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
			 ONLY=$(ONLY) \

.PHONY: clobber clean

clean:
	$(IDRIS2) --clean circuits.ipkg
	${MAKE} -C tests clean

clobber: clean
	$(IDRIS2) --clean idealised.ipkg
	$(IDRIS2) --clean netlist.ipkg
	${MAKE} -C tests clobber
	${RM} -rf build/
