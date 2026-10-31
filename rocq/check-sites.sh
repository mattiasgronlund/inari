#!/usr/bin/env bash
# Runs the greps that rocq/README.md, "What is assumed", gives for the places
# in `src` that make an `Interval` or a `DecInterval`, which `Valid.v` and
# `ComCommon.v` rely on, and checks that they find the lines listed in
# rocq/sites.txt. A line is compared without its line number and indentation,
# so the check fails if a line is added, removed, changed or moved to another
# file, but not if it only moves within its file. The grep com-struct also
# finds the declarations of the fields of `DecInterval`, so the check fails if
# the line of one of them changes, for example if it gains `pub(crate)`. It
# also fails if the README no longer gives one of the greps, or if one of the
# two that must find nothing finds something. Which of the lines make an
# interval, and the rest of the README's argument, is still checked by reading.
#
# Usage: rocq/check-sites.sh [--update]
# With --update, it writes the lines that it finds to rocq/sites.txt.
# `git grep` searches only the files that Git tracks, so `git add` a new file
# before running this.
set -euo pipefail
export LC_ALL=C
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

# A Git setting must not change how the greps read their patterns or what they
# print. Options on the command line, such as `-E`, still override these.
export GIT_CONFIG_COUNT=3 \
  GIT_CONFIG_KEY_0=grep.patternType GIT_CONFIG_VALUE_0=basic \
  GIT_CONFIG_KEY_1=grep.column GIT_CONFIG_VALUE_1=false \
  GIT_CONFIG_KEY_2=color.grep GIT_CONFIG_VALUE_2=never

# The README's greps, verbatim.
valid_rep="git grep -nE '\brep *:' -- src ':!src/simd'"
valid_raw="git grep -n 'with_infsup_raw\|transmute' -- src ':!src/simd'"
valid_shorthand="git grep -nE '\{ *rep *[,}]' -- src"
valid_assign="git grep -nE '\.rep *=[^=]' -- src ':!src/simd'"
com_unchecked="git grep -n 'new_unchecked\|transmute' -- src"
com_struct="git grep -nE '(Self|DecInterval) *\{|\b[xd]: ' -- src/interval/dec_interval.rs"

status=0

for cmd in "$valid_rep" "$valid_raw" "$valid_shorthand" "$valid_assign" \
  "$com_unchecked" "$com_struct"; do
  if ! grep -qF -- "\`$cmd\`" rocq/README.md; then
    echo "check-sites: rocq/README.md no longer gives \`$cmd\`." \
      "Change the greps in the README and in rocq/check-sites.sh together." >&2
    status=1
  fi
done

# Runs a grep. `git grep` exits with 1 if it finds nothing.
run() {
  eval "$1" || [ $? -eq 1 ] || {
    echo "check-sites: \`$1\` failed." >&2
    exit 2
  }
}

# Checks that a grep finds nothing, as the argument for Valid.v in the README
# needs, and says what to write instead.
nothing() {
  local out
  out=$(run "$1")
  if [ -n "$out" ]; then
    printf '%s\n' "check-sites: \`$1\` must find nothing, but finds:" "$out" \
      "$2" >&2
    status=1
  fi
}

nothing "$valid_shorthand" "Write the field of an \`Interval\` struct \
expression as \`rep: ...\`, so that the grep for \`rep:\` finds it."
nothing "$valid_assign" "Make a new \`Interval\` rather than assign to \`rep\`."

# Prints the lines that a grep finds as `<name> <path>: <line>`, without the
# line number and indentation.
sites() {
  run "$2" | sed -E "s/^([^:]*):[0-9]+:[[:space:]]*/$1 \\1: /"
}

# `&&`, as `set -e` does not apply inside `$(...)`.
found=$(
  {
    sites valid-rep "$valid_rep" &&
      sites valid-raw "$valid_raw" &&
      sites com-unchecked "$com_unchecked" &&
      sites com-struct "$com_struct"
  } | sort
)
found="# The lines that the greps in rocq/check-sites.sh find, sorted, without
# line numbers and indentation.
# Update this file with \`rocq/check-sites.sh --update\` after the changes that
# the script's message names.
$found"

if [ "${1-}" = --update ]; then
  printf '%s\n' "$found" >rocq/sites.txt
  exit "$status"
fi

if ! diff -u --label rocq/sites.txt --label 'found now' rocq/sites.txt - \
  <<<"$found" >&2; then
  cat >&2 <<'EOF'
check-sites: the lines above differ from rocq/sites.txt (-: listed there,
+: found now), so a place that makes an `Interval` or a `DecInterval` may have
been added, removed or changed. For each such line:
- valid-rep and valid-raw are for the places that make an `Interval`. If the
  line is in a constructor or in an operation that is proved, update its model
  in rocq/theories/Model.v, and if it is new, add a `made` or `dmade`
  constructor for it in rocq/theories/Valid.v and its case of `made_valid`.
  If it is in an operation that is not proved, name that operation under
  "What is not proved yet" in rocq/README.md.
- com-unchecked and com-struct are for the places that make a `DecInterval`.
  For such a place, update its model in rocq/theories/Model.v and its theorem
  in rocq/theories/ComCommon.v, which shows that a `DecInterval` is `com` only
  if its interval is common, and for a new constructor, add a `dmade`
  constructor as above. com-struct finds the declarations of the fields of
  `DecInterval` and its one struct expression, in src/interval/dec_interval.rs.
  Keep the fields private (no `pub`): the README's argument for ComCommon.v
  needs the compiler to reject a struct expression of `DecInterval`, and an
  assignment to one of its fields, outside that file.
- Then update the two bullets in rocq/README.md, "What is assumed", that give
  these greps, and run `rocq/check-sites.sh --update`.
A line that makes neither, such as a signature `-> Self {` or a comment, needs
nothing for this check but the update.
EOF
  status=1
fi

exit "$status"
