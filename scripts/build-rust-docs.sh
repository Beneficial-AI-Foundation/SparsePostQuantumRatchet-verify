#!/bin/bash
# Build the spqr rustdoc and inject the per-function Lean verification panels.
#
# The docs are built with `--features extraction` — the exact configuration
# Aeneas translated to Lean (see aeneas-config.yml). This matters semantically:
# e.g. `mul2_u16` dispatches to an arch-accelerated branch under default
# features that is NOT covered by the Lean proofs; with the extraction feature
# the verified functions only execute the unaccelerated implementations. (The
# private `accelerated` helper modules are still compiled on some arches and
# appear in the docs, but carry no panels and are outside the verified scope.)
# `--document-private-items` is required because the verified functions live
# in pub(crate) modules.
#
# The Rust toolchain is pinned: the injector post-processes rustdoc's HTML,
# whose layout/anchor scheme is explicitly unstable across rustdoc versions.
#
# Requires: rustup toolchain $RUST_DOCS_TOOLCHAIN, protoc (build.rs/prost),
# node + npx (tsx), and functions.json (`lake exe docsjson`).

set -euo pipefail

HERE=$(cd "$(dirname "$0")"; pwd)
ROOT=$HERE/..

RUST_DOCS_TOOLCHAIN=${RUST_DOCS_TOOLCHAIN:-1.94.1}
TARGET_DIR=$ROOT/target/docs-build

FUNCTIONS_JSON=$TARGET_DIR/functions.json
if [ ! -f "$FUNCTIONS_JSON" ]; then
  echo "error: $FUNCTIONS_JSON not found — run 'lake exe docsjson' first" >&2
  exit 1
fi

# Fresh output every run: the HTML is post-processed in place, and cargo's
# incremental doc builds can leave stale pages (e.g. for a function whose spec
# was removed) that a partial rebuild would never clean up.
rm -rf "$TARGET_DIR/doc"

cargo "+$RUST_DOCS_TOOLCHAIN" rustdoc \
  --manifest-path "$ROOT/Cargo.toml" \
  --target-dir "$TARGET_DIR" \
  --lib \
  --features extraction \
  -- --document-private-items

echo "Injecting Lean verification panels into rustdoc HTML..."
npx tsx "$ROOT/scripts/inject-lean-verification.ts" \
  --rustdoc-root "$TARGET_DIR/doc" \
  --functions "$FUNCTIONS_JSON" \
  --rust-version "$(rustc "+$RUST_DOCS_TOOLCHAIN" --version)"

echo "Rust documentation with Lean panels built at $TARGET_DIR/doc/"
