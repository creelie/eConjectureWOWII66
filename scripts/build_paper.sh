#!/usr/bin/env bash
# build_paper.sh -- build the paper and its submission files into dist/.
#
#   dist/wowii66-forest-number.pdf           the compiled paper
#   dist/wowii66-forest-number-tex.zip       main.tex with the figures as PNG (and their TikZ sources)
#   dist/wowii66-forest-number-arxiv.tar.gz  main.tex and the figures as PDF, ready for arXiv
#
# Needs pdflatex with amsart, tikz and hyperref; pdftoppm (poppler) for the PNG
# figures; zip and tar.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PAPER="$ROOT/preprintWOWIIConjecture66"
DIST="$ROOT/dist"
NAME=wowii66-forest-number
FIGS="g10 chain"
mkdir -p "$DIST"

latex() { pdflatex -interaction=nonstopmode -halt-on-error "$@" > /dev/null; }

echo "== figures"
cd "$PAPER/figures"
for f in $FIGS; do
  latex "$f.tex"
  pdftoppm -png -r 200 -singlefile "$f.pdf" "$f"
  rm -f "$f.aux" "$f.log"
done

echo "== paper"
cd "$PAPER"
latex main.tex
latex main.tex
if grep -q "Overfull\|undefined" main.log; then
  grep "Overfull\|undefined" main.log
  echo "build_paper.sh: fix the warnings above" >&2
  exit 1
fi
cp main.pdf "$DIST/$NAME.pdf"

echo "== tex.zip (figures as PNG)"
STAGE="$(mktemp -d)"
trap 'rm -rf "$STAGE"' EXIT
mkdir -p "$STAGE/$NAME/figures"
sed 's#\\includegraphics\(\[[^]]*\]\)\?{figures/\([a-z0-9]*\)}#\\includegraphics\1{figures/\2.png}#' \
  main.tex > "$STAGE/$NAME/main.tex"
for f in $FIGS; do cp "figures/$f.png" "figures/$f.tex" "$STAGE/$NAME/figures/"; done
( cd "$STAGE/$NAME" && latex main.tex && latex main.tex && rm -f main.aux main.log main.out main.pdf )
rm -f "$DIST/$NAME-tex.zip"
( cd "$STAGE" && zip -qr "$DIST/$NAME-tex.zip" "$NAME" )

echo "== arXiv tarball (figures as PDF)"
mkdir -p "$STAGE/arxiv/figures"
cp main.tex "$STAGE/arxiv/"
for f in $FIGS; do cp "figures/$f.pdf" "$STAGE/arxiv/figures/"; done
( cd "$STAGE/arxiv" && latex main.tex && latex main.tex && rm -f main.aux main.log main.out main.pdf )
tar -czf "$DIST/$NAME-arxiv.tar.gz" -C "$STAGE/arxiv" .

rm -f main.aux main.log main.out
ls -l "$DIST"
