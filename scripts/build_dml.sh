#!/usr/bin/env bash
# build_dml.sh -- build the Discrete Mathematics Letters version of the paper (same mathematics
# as preprintWOWIIConjecture66/main.tex, in the journal's DML template) into build/submission-dml/:
#
#   wowii66-forest-number-dml.pdf         the manuscript to e-mail to the journal
#   wowii66-forest-number-dml-source.zip  its LaTeX source with the figures as PNG
#
# Run scripts/build_paper.sh first (it makes the figures). Needs pdflatex and zip.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PAPER="$ROOT/preprintWOWIIConjecture66"
OUT="$ROOT/build/submission-dml"
NAME=wowii66-forest-number-dml
mkdir -p "$OUT"
STAGE="$(mktemp -d)"
trap 'rm -rf "$STAGE"' EXIT
latex() { pdflatex -interaction=nonstopmode -halt-on-error "$@" > /dev/null; }

mkdir -p "$STAGE/$NAME/figures"
sed 's#\\includegraphics\(\[[^]]*\]\)\?{figures/\([a-z0-9]*\)}#\\includegraphics\1{figures/\2.png}#' \
  "$PAPER/dml/wowii66-dml.tex" > "$STAGE/$NAME/$NAME.tex"
for f in g10 chain; do cp "$PAPER/figures/$f.png" "$STAGE/$NAME/figures/"; done
mkdir -p "$STAGE/pdf/figures"
cp "$PAPER/dml/wowii66-dml.tex" "$STAGE/pdf/$NAME.tex"
for f in g10 chain; do cp "$PAPER/figures/$f.pdf" "$STAGE/pdf/figures/"; done
( cd "$STAGE/pdf" && latex "$NAME.tex" && latex "$NAME.tex" )
# the template's own header box is 15pt too wide; any other warning is an error
if grep "Overfull\|undefined" "$STAGE/pdf/$NAME.log" | grep -v "15.0pt too wide"; then
  echo "build_dml.sh: fix the warnings above" >&2
  exit 1
fi
pages=$(pdfinfo "$STAGE/pdf/$NAME.pdf" 2>/dev/null | awk '/^Pages:/ {print $2}')
if [ -n "$pages" ] && [ "$pages" -gt 8 ]; then echo "build_dml.sh: $pages pages, the limit is 8" >&2; exit 1; fi
cp "$STAGE/pdf/$NAME.pdf" "$OUT/"
( cd "$STAGE/$NAME" && latex "$NAME.tex" && latex "$NAME.tex" && rm -f "$NAME".aux "$NAME".log "$NAME".out "$NAME".pdf )
rm -f "$OUT/$NAME-source.zip"
( cd "$STAGE" && zip -qr "$OUT/$NAME-source.zip" "$NAME" )
ls -l "$OUT"
