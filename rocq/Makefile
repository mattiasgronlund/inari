# Checks the proofs with Rocq 9.1 and Flocq 4.2.2 (see README.md).

# Warnings are errors, like `-Dwarnings` for the Rust code.
COQEXTRAFLAGS := -w +default
export COQEXTRAFLAGS

# The recipes of this Makefile run under bash with `-euo pipefail`
# (.SHELLFLAGS takes GNU Make 3.82 or later), not under /bin/sh, which is
# dash on Debian and Ubuntu, and the dash of Debian 12 and Ubuntu 24.04 has
# no pipefail. A pipe then fails when any of its stages fails, not only when
# its last one does, and a recipe line stops at the first command that fails,
# unless the line tests that command's status, as `if` and `||` do. A pipe
# negated with `!`, as in `examples`, passes when one of its stages fails.
# The recipes of RocqMakefile, which `proofs` runs, still run under /bin/sh,
# since make ignores SHELL in the environment and RocqMakefile sets none.
SHELL := bash
.SHELLFLAGS := -euo pipefail -c

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

# STRIP prints each line of a Rocq file without its comments and strings, for
# `examples`. As in Rocq, comments nest, and a string, in code or in a
# comment, runs to the next `"`, so that the `(*` in `"(*"` opens no comment.
# Rocq writes a `"` in a string as `""`, which this reads as two strings, to
# the same effect. `d`, the depth of comments, and `s`, 1 in a string, carry
# over from one line to the next.
STRIP := awk '{ \
	out = ""; \
	for (i = 1; i <= length($$0); i++) { \
		c = substr($$0, i, 1); \
		if (c == "\"") { s = !s; continue } \
		if (s) continue; \
		if (substr($$0, i, 2) == "(*") { d++; i++; continue } \
		if (d && substr($$0, i, 2) == "*)") { d--; i++; continue } \
		if (!d) out = out c \
	} \
	print out }'

# The theorems that Assumptions.v prints and the constructors of `made` and
# `dmade` that quantify over an MPFR must each have an `Example` in
# theories/MpfrExamples.v, which applies it to the ideal MPFR. `Search` prints
# each name that it finds as `name:` at the start of a line, with the type
# after it or on indented lines. By default it hides the names whose qualified
# name contains `Private_`, `_subproof` or `_subterm`, and Assumptions.v has
# it show them. `assumptions` removes MpfrSearch.out and MpfrSearchValid.out
# before Assumptions.v writes them at its end, and fails on an error in
# Assumptions.v. If one of them is still missing or empty when `examples`
# runs, usually because its `Redirect` is gone, its `Search` found nothing,
# or `examples` ran without `assumptions` (`make -o assumptions`), the check
# stops there.
# MpfrExamples.out lists the names in MpfrSearch.out that Assumptions.v prints
# (`uniq -d` keeps the names that both lists have), and those in
# MpfrSearchValid.out, from Valid.v, other than the induction principles of
# `made` and `dmade`, whose names end in `_ind` or `_sind`. These must be the
# names of the `Example`s, of which only the lines
# `Example <name>_ideal := ltac:(mpfr_example <name>).` are read. Assumptions.v
# and MpfrExamples.v are read without their comments and strings (STRIP), so a
# `Print Assumptions` or an `Example` in a comment or a string does not count.
# The check stops at a line of Assumptions.v that mentions `Assumptions` but is
# not `Print Assumptions <name>.`, as it would not read the name of the theorem
# that such a line prints. Names are compared as written, so a theorem that
# Assumptions.v prints by another name than the one that `Search` gives it, the
# shortest that refers to it there, need not have an `Example`.
examples: assumptions
	for f in MpfrSearch.out MpfrSearchValid.out; do test -s $$f || { \
		echo "$$f" 'is missing or empty. A `Redirect` at the end of Assumptions.v' \
			'writes it, so the usual causes are a removed `Redirect`, a `Search`' \
			'that finds nothing, or `examples` run without `assumptions`, which' \
			'compiles Assumptions.v.' >&2; \
		exit 1; }; done
	! $(STRIP) Assumptions.v | grep -n Assumptions \
		| grep -v '^[0-9]*:Print Assumptions [^ ]*\.$$' >&2 || { \
		echo 'Each line of Assumptions.v above, after its number and without its' \
			'comments and strings, mentions `Assumptions` but is not' \
			'`Print Assumptions <name>.`, so the check of the `Example`s cannot' \
			'read which theorem it prints. Write each as `Print Assumptions <name>.`' \
			'on a line of its own.' >&2; \
		exit 1; }
	{ { $(STRIP) Assumptions.v | sed -n 's/^Print Assumptions \(.*\)\.$$/\1/p' \
		| LC_ALL=C sort -u; \
		sed -n 's/^\([^ :]*\):.*/\1/p' MpfrSearch.out | LC_ALL=C sort -u; } \
		| LC_ALL=C sort | LC_ALL=C uniq -d; \
		sed -n 's/^\([^ :]*\):.*/\1/p' MpfrSearchValid.out | grep -v -e '_ind$$' -e '_sind$$'; } \
		| LC_ALL=C sort -u > MpfrExamples.out
	$(STRIP) theories/MpfrExamples.v \
		| sed -n 's/^Example \([A-Za-z0-9_]*\)_ideal := ltac:(mpfr_example \1)\.$$/\1/p' \
		| LC_ALL=C sort | diff -u MpfrExamples.out - || { \
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
