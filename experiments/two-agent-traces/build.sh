#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
experiment=experiments/two-agent-traces
build_dir="$experiment/build"
mkdir -p "$build_dir"
lake env lean "$experiment/TraceRun.lean" > "$build_dir/lean.log" 2>&1
cat "$experiment/TraceRun.lean" "$experiment/ReviewChecks.lean" > "$build_dir/ReviewCombined.lean"
lake env lean "$build_dir/ReviewCombined.lean" > "$build_dir/axioms.log" 2>&1
for pass in 1 2; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$build_dir" \
    "$experiment/paper.tex" > "$build_dir/pdflatex-$pass.log" 2>&1
done
cp "$build_dir/paper.pdf" "$experiment/paper.pdf"
echo "Lean proofs, review checks, axiom audit, and PDF build passed."
