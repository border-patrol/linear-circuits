IDRIS2=idris2
HYPERFINE=hyperfine

TARGETDIR = ${CURDIR}/build/exec

bopts ?=


.PHONY: netlist netlist-test-bin netlist-test-run netlist-test-update

netlist:
	idris2 --build netlist.ipkg


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
	idris2 --build idealised.ipkg


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
	idris2 --clean circuits.ipkg
	make -C tests clean

clobber: clean
	${MAKE} -C tests clobber
	${RM} -rf build/