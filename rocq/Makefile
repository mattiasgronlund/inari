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

all: assumptions examples

proofs: RocqMakefile
	$(MAKE) -f RocqMakefile

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

# `Print Assumptions` prints each axiom as `name : type`, with the type
# possibly continued on indented lines. Assumptions.v also writes the output
# of two `Search`es to MpfrSearch.out and MpfrSearchValid.out, for `examples`.
assumptions: proofs
	rm -f MpfrSearch.out MpfrSearchValid.out
	rocq compile $(COQEXTRAFLAGS) -output-directory . -R theories Inari Assumptions.v \
		| sed -n 's/^\([^ ]*\) :.*/\1/p' | LC_ALL=C sort -u > Assumptions.out
	printf '%s\n' $(AXIOMS) | LC_ALL=C sort | diff -u - Assumptions.out

# The theorems that Assumptions.v prints and the constructors of `made` and
# `dmade` that quantify over an MPFR must each have an `Example` in
# theories/MpfrExamples.v, which applies it to the ideal MPFR. `Search` prints
# each name that it finds as `name:` at the start of a line, with the type
# after it or on indented lines. MpfrExamples.out lists the names in
# MpfrSearch.out that Assumptions.v prints (`uniq -d` keeps the names that
# both lists have), and those in MpfrSearchValid.out, from Valid.v, other than
# the induction principles of `made` and `dmade`, whose names end in `_ind` or
# `_sind`. These must be the names of the `Example`s, of which only the lines
# `Example <name>_ideal := ltac:(mpfr_example <name>).` are read. Names are
# compared as written, so a theorem that Assumptions.v prints by another name
# than the one that `Search` gives it, the shortest that refers to it there,
# need not have an `Example`.
examples: assumptions
	{ { sed -n 's/^Print Assumptions \(.*\)\.$$/\1/p' Assumptions.v | LC_ALL=C sort -u; \
		sed -n 's/^\([^ :]*\):.*/\1/p' MpfrSearch.out | LC_ALL=C sort -u; } \
		| LC_ALL=C sort | LC_ALL=C uniq -d; \
		sed -n 's/^\([^ :]*\):.*/\1/p' MpfrSearchValid.out | grep -v -e '_ind$$' -e '_sind$$'; } \
		| LC_ALL=C sort -u > MpfrExamples.out
	sed -n 's/^Example \([A-Za-z0-9_]*\)_ideal := ltac:(mpfr_example \1)\.$$/\1/p' \
		theories/MpfrExamples.v | LC_ALL=C sort | diff -u MpfrExamples.out - || { \
		echo 'The names above differ between MpfrExamples.out (-), which must each' \
			'have an `Example`, and the `Example`s in theories/MpfrExamples.v (+).' \
			'Write each as `Example <name>_ideal := ltac:(mpfr_example <name>).` on' \
			'one line, and remove those of names that are not in MpfrExamples.out.' >&2; \
		exit 1; }

clean:
	if [ -f RocqMakefile ]; then $(MAKE) -f RocqMakefile cleanall; fi
	rm -f RocqMakefile RocqMakefile.conf .RocqMakefile.d
	rm -f Assumptions.vo Assumptions.vok Assumptions.vos Assumptions.glob
	rm -f .Assumptions.aux Assumptions.out
	rm -f MpfrSearch.out MpfrSearchValid.out MpfrExamples.out

.PHONY: all proofs assumptions examples clean
