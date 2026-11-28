#!/bin/sh
# Checks the blueprint sources without plasTeX.
#
#   blueprint/tools/check_names.sh               names, labels, and `lake exe checkdecls`
#   blueprint/tools/check_names.sh --list FILE   names against a list of declarations (no Lean)
#   blueprint/tools/check_names.sh --make-list   write blueprint/decl_names.txt (needs `lake build`)
#   blueprint/tools/check_names.sh --extract     only write blueprint/lean_decls
#
# What it does:
#   1. Extracts every name of every \lean{...} of blueprint/src (comments removed, commas and line
#      breaks handled) into blueprint/lean_decls, one per line: the file that leanblueprint writes
#      and that the CI gives to checkdecls.
#   2. Checks the labels: no \label is defined twice, every label of \uses{...} and \proves{...}
#      exists, and the labels of chapters/map/KEY.tex begin with `kind:KEY` (see blueprint/README.md).
#      The same for the references: no \bibitem key twice, every key of \cite{...} exists. It
#      counts the entries marked `% unverified`.
#   3. Checks the names of the `% uses-lean:` comments like those of \lean{...}.
#   4. Checks that every name is a declaration: with `lake exe checkdecls` (the check of the CI; it
#      needs the compiled project), or, with --list FILE, against a list made by --make-list.
#      The list has the declarations of this repository only: a name of Mathlib or of Lean is
#      reported as "not in the list" and must be checked with the full check.
#
# Exit status 0 when everything passes, 1 otherwise. POSIX sh and awk; run from anywhere.
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
src="$root/blueprint/src"
decls="$root/blueprint/lean_decls"
mode=full
list=
case "${1:-}" in
  "") ;;
  --list) mode=list; list="${2:?--list needs a file}" ;;
  --make-list) mode=makelist ;;
  --extract) mode=extract ;;
  *) sed -n '2,8p' "$0"; exit 1 ;;
esac

if [ "$mode" = makelist ]; then
  cd "$root" || exit 1
  roots=$(grep -E '^roots = ' lakefile.toml | grep -o '"[^"]*"' | tr -d '"' | tr '\n' ' ')
  # shellcheck disable=SC2086
  lake env lean --run blueprint/tools/DeclNames.lean $roots > blueprint/decl_names.txt || exit 1
  echo "wrote blueprint/decl_names.txt: $(wc -l < blueprint/decl_names.txt | tr -d ' ') declarations"
  exit 0
fi

files=$(find "$src" -name '*.tex' | LC_ALL=C sort)
tmp=$(mktemp -d)
trap 'rm -r "$tmp"' EXIT

# One awk pass per file. It prints records `kind<TAB>file:line<TAB>value`:
#   lean   a name of \lean{...}          label  a \label{...}          bib   a \bibitem key
#   uses   a label of \uses or \proves   ulean  a `% uses-lean:` name   cite  a \cite key
for f in $files; do
  awk -v file="${f#"$root"/}" '
    function emit(kind, line, list,    n, i, parts, v) {
      n = split(list, parts, ",")
      for (i = 1; i <= n; i++) {
        v = parts[i]; gsub(/^[ \t]+|[ \t]+$/, "", v)
        if (v != "") print kind "\t" file ":" line "\t" v
      }
    }
    {
      raw = $0
      if (match(raw, /^[ \t]*%[ \t]*uses-lean:/)) {
        emit("ulean", NR, substr(raw, RSTART + RLENGTH)); next
      }
      # remove comments: a % that is not escaped, to the end of the line
      out = ""; s = raw
      while ((p = index(s, "%")) > 0) {
        if (p > 1 && substr(s, p - 1, 1) == "\\") { out = out substr(s, 1, p); s = substr(s, p + 1) }
        else { s = substr(s, 1, p - 1); break }
      }
      line = out s
      if (pending != "") {            # inside a \lean{ or \uses{ that did not close on its line
        q = index(line, "}")
        if (q == 0) { buf = buf " " line; next }
        emit(pending, start, buf " " substr(line, 1, q - 1)); pending = ""; line = substr(line, q + 1)
      }
      while (match(line, /\\(lean|uses|proves|label|bibitem|cite)[ \t]*(\[[^]]*\])?[ \t]*\{/)) {
        cmd = substr(line, RSTART + 1, RLENGTH - 1); sub(/[^a-z].*$/, "", cmd)
        kind = (cmd == "uses" || cmd == "proves") ? "uses" : (cmd == "bibitem") ? "bib" : cmd
        rest = substr(line, RSTART + RLENGTH)
        q = index(rest, "}")
        if (q == 0) { pending = kind; start = NR; buf = rest; line = ""; break }
        emit(kind, NR, substr(rest, 1, q - 1)); line = substr(rest, q + 1)
      }
    }
    END { if (pending != "") print "open\t" file ":" start "\tunclosed brace" }
  ' "$f"
done > "$tmp/records"

fail=0
say() { echo "$*"; fail=1; }

awk -F'\t' '$1 == "open" { print "ERROR " $2 ": \\lean, \\uses or \\label with an unclosed brace" }' "$tmp/records" > "$tmp/open"
[ -s "$tmp/open" ] && { cat "$tmp/open"; fail=1; }

awk -F'\t' '$1 == "lean" { print $3 }' "$tmp/records" | LC_ALL=C sort -u > "$decls"
awk -F'\t' '$1 == "ulean" { print $3 }' "$tmp/records" | LC_ALL=C sort -u > "$tmp/ulean"
nlean=$(wc -l < "$decls" | tr -d ' ')
echo "names: $nlean distinct in \\lean{...} -> blueprint/lean_decls; $(wc -l < "$tmp/ulean" | tr -d ' ') in uses-lean comments"
[ "$mode" = extract ] && exit $fail

# Labels.
awk -F'\t' '$1 == "label" { n[$3]++; where[$3] = where[$3] " " $2 }
  END { for (l in n) if (n[l] > 1) print "ERROR label defined " n[l] " times: " l " (" where[l] " )" }' \
  "$tmp/records" | LC_ALL=C sort > "$tmp/dups"
[ -s "$tmp/dups" ] && { cat "$tmp/dups"; fail=1; }
awk -F'\t' '$1 == "label" { def[$3] = 1 } $1 == "uses" { use[$3] = $2 }
  END { for (l in use) if (!(l in def)) print "ERROR " use[l] ": \\uses a label that does not exist: " l }' \
  "$tmp/records" | LC_ALL=C sort > "$tmp/undef"
[ -s "$tmp/undef" ] && { cat "$tmp/undef"; fail=1; }
awk -F'\t' '$1 == "label" && $2 ~ /chapters\/map\// {
    key = $2; sub(/^.*chapters\/map\//, "", key); sub(/\.tex:.*$/, "", key)
    if ($3 !~ ("^(chap|sec|def|thm|lem|prop|cor):" key "(-|$)")) print "ERROR " $2 ": label " $3 " must begin with kind:" key
  }' "$tmp/records" > "$tmp/prefix"
[ -s "$tmp/prefix" ] && { cat "$tmp/prefix"; fail=1; }
echo "labels: $(awk -F'\t' '$1 == "label"' "$tmp/records" | wc -l | tr -d ' ') defined, $(awk -F'\t' '$1 == "uses" { print $3 }' "$tmp/records" | LC_ALL=C sort -u | wc -l | tr -d ' ') used"

# References.
awk -F'\t' '$1 == "bib" { n[$3]++; where[$3] = where[$3] " " $2 }
  END { for (k in n) if (n[k] > 1) print "ERROR \\bibitem defined " n[k] " times: " k " (" where[k] " )" }' \
  "$tmp/records" | LC_ALL=C sort > "$tmp/bibdups"
[ -s "$tmp/bibdups" ] && { cat "$tmp/bibdups"; fail=1; }
awk -F'\t' '$1 == "bib" { def[$3] = 1 } $1 == "cite" { use[$3] = $2 }
  END { for (k in use) if (!(k in def)) print "ERROR " use[k] ": \\cite of a reference that does not exist: " k }' \
  "$tmp/records" | LC_ALL=C sort > "$tmp/bibundef"
[ -s "$tmp/bibundef" ] && { cat "$tmp/bibundef"; fail=1; }
# shellcheck disable=SC2086
echo "references: $(awk -F'\t' '$1 == "bib"' "$tmp/records" | wc -l | tr -d ' ') entries, $(cat $files | grep -c 'bibitem.*%[ ]*unverified') marked unverified"

# Names.
if [ "$mode" = list ]; then
  [ -r "$list" ] || { echo "ERROR cannot read the list $list"; exit 1; }
  LC_ALL=C sort -u "$list" > "$tmp/known"
  LC_ALL=C comm -23 "$decls" "$tmp/known" > "$tmp/missing"
  LC_ALL=C comm -23 "$tmp/ulean" "$tmp/known" > "$tmp/umissing"
  if [ -s "$tmp/missing" ] || [ -s "$tmp/umissing" ]; then
    while read -r name; do
      echo "ERROR not in the list: $name ($(awk -F'\t' -v n="$name" '($1 == "lean" || $1 == "ulean") && $3 == n { printf "%s ", $2 }' "$tmp/records"))"
    done < "$tmp/missing"
    while read -r name; do
      echo "ERROR not in the list (uses-lean): $name ($(awk -F'\t' -v n="$name" '$1 == "ulean" && $3 == n { printf "%s ", $2 }' "$tmp/records"))"
    done < "$tmp/umissing"
    fail=1
  fi
else
  cat "$decls" "$tmp/ulean" | LC_ALL=C sort -u > "$tmp/all"
  (cd "$root" && lake exe checkdecls "$tmp/all") || fail=1
fi

if [ $fail -eq 0 ]; then echo "OK"; else echo "FAILED"; fi
exit $fail
