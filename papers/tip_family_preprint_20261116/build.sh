#!/usr/bin/env bash
# Reproducible, plain-pdflatex build; no repository source changes.
set -euo pipefail
here="$(cd -- "$(dirname -- "$0")" && pwd)"
cd "$here"
command -v pdflatex >/dev/null || { echo >&2 "pdflatex is required"; exit 127; }
command -v bibtex >/dev/null || { echo >&2 "bibtex is required"; exit 127; }
pdflatex -interaction=nonstopmode -file-line-error -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -file-line-error -halt-on-error main.tex
pdflatex -interaction=nonstopmode -file-line-error -halt-on-error main.tex
test -s main.pdf
echo "Built $here/main.pdf"
