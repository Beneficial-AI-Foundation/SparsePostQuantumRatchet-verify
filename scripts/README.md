# Scripts

## Commands

- **`npm run aeneas-install`** — Download the aeneas + charon binaries from the pinned GitHub release into `.aeneas/`, and install the Rust nightly `charon-driver` needs. Skips the download if the installed version already matches the pinned tag.
- **`npm run aeneas-extract`** — Run the extraction pipeline: charon (Rust → LLBC) → aeneas (LLBC → Lean) → post-extraction tweaks.
- **`npm run src-diff`** — Generate `src-modifications.diff` comparing local `src/` against the pinned upstream commit.

## Configuration

All extraction options live in `aeneas-config.yml` at the project root.

## Updating the aeneas version

The aeneas **release tag** is pinned in two places that must be kept in sync:

1. `aeneas-config.yml` — `aeneas.tag` (used by the install/extract scripts for the binaries)
2. `lakefile.toml` — `rev` in the aeneas `[[require]]` block (used by Lake for the Lean backend dependency)
