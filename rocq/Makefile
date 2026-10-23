# Checks the proofs with Rocq 9.1 and Flocq 4.2.2 (see README.md).

# Warnings are errors, like `-Dwarnings` for the Rust code.
COQEXTRAFLAGS := -w +default
export COQEXTRAFLAGS

# The axioms that the theorems may depend on: those of the real numbers in
# Stdlib, and excluded middle, which Flocq uses. Any other axiom, such as a
# proof left `Admitted`, fails the build.
AXIOMS := \
	ClassicalDedekindReals.sig_forall_dec \
	ClassicalDedekindReals.sig_not_dec \
	Classical_Prop.classic \
	FunctionalExtensionality.functional_extensionality_dep

all: assumptions

proofs: RocqMakefile
	$(MAKE) -f RocqMakefile

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

# `Print Assumptions` prints each axiom as `name : type`, with the type
# possibly continued on indented lines.
assumptions: proofs
	rocq compile $(COQEXTRAFLAGS) -R theories Inari Assumptions.v \
		| sed -n 's/^\([^ ]*\) :.*/\1/p' | LC_ALL=C sort -u > Assumptions.out
	printf '%s\n' $(AXIOMS) | LC_ALL=C sort | diff -u - Assumptions.out

clean:
	if [ -f RocqMakefile ]; then $(MAKE) -f RocqMakefile cleanall; fi
	rm -f RocqMakefile RocqMakefile.conf .RocqMakefile.d
	rm -f Assumptions.vo Assumptions.vok Assumptions.vos Assumptions.glob
	rm -f .Assumptions.aux Assumptions.out

.PHONY: all proofs assumptions clean
