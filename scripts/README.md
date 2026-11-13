# Scripts

## Commands

- **`npm run aeneas-install`** — Download the aeneas + charon binaries from the pinned GitHub release into `.aeneas/`, and install the Rust nightly `charon-driver` needs. Skips the download if the installed version already matches the pinned tag.
- **`npm run aeneas-extract`** — Run the extraction pipeline: apply the Rust translation patches → charon (Rust → LLBC) → revert the patches → aeneas (LLBC → Lean) → post-extraction tweaks. Refuses to run if the installed aeneas does not match the pinned tag.
- **`npm run src-diff`** — Generate `src-modifications.diff` comparing local `src/` against the pinned upstream commit.
- **`npm run split-probe-lean`** — Reproducibly split complete Lean source files from `.verilib/probes/lean_extract.json` into dependency-safe generation and test sets under `data/probe-lean-split/`, emitting only `def` declarations. `generation-files.txt` and `test-files.txt` contain the complete file partition; the JSONL files contain the definitions to generate or test. No file occurs on both sides, and the generation file set is dependency-closed. Pass options after `--`, for example `npm run split-probe-lean -- --seed 42 --generation-ratio 0.8`.
- **`npm run generate-lean-definitions -- <file.lean> [more.lean ...]`** — Run a read-only Codex agent once per input Lean file and save proposed reusable `def` or `abbrev` declarations, their purpose, and possible reuse sites to `data/generated-definitions.json`. Source files are not edited. Pass `-o path.json`, `--model MODEL`, or `--timeout SECONDS` after the file arguments as needed. To analyze the existing training split, use `npm run generate-lean-definitions -- --files-from data/probe-lean-split/generation-files.txt`; this can make many Codex calls. Proposals need review and Lean compilation before use.
- **`npm run apply-generated-definitions`** — Append proposals from `data/generated-definitions.json` to their generation files and run `lake build` on every generation module. The command rejects proposals for held-out test files and restores all edited source files if compilation fails. Review proposal meaning and reuse before applying; compilation checks Lean correctness, not semantic value.
- **`npm run patches-check`** — Check the translation patches: each applies on its own, all apply and revert in forward and reverse order, and the working tree is unchanged afterwards.

## Configuration

Extraction options live in `aeneas-config.yml` at the project root, except Charon's `exclude`/`opaque`
lists, which `charon cargo` reads from the `[package.metadata.charon]` section of `Cargo.toml`.

## Translation patches

The Rust sources (`src/`, `build.rs`, and `Cargo.toml` apart from its `[package.metadata.charon]`
section) are kept identical to the upstream commit named in `aeneas-config.yml`. Every change needed for the translation is a patch in
`translation-patches/`, one function per patch, applied only while Charon runs:

- File name: `<file-stem>-<function>.patch`, with `-<Type>` before the function only when the
  name alone is ambiguous within that Rust file.
- Body: `git diff -W -- <file>` from the repository root (needs `*.rs diff=rust` in
  `.gitattributes`), so the whole function is shown.
- Header (free text before the first `diff --git`, ignored by `git apply`):

  ```
  Translation patch: <Rust item>

  Change: <one line: what the rewrite does>
  Why: <the Aeneas/Charon limitation, with the issue number if known>
  Behaviour: identical. | <exactly what differs>
  Relies on: <a fact not visible in the diff>      (only when there is one)
  ```

## Updating the aeneas version

The aeneas **release tag** is pinned only in `lakefile.toml` (`rev` in the aeneas `[[require]]`
block). The install and extract scripts read it from there. See `doc/aeneas.md`.
