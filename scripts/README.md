# Scripts

## Commands

- **`npm run aeneas-install`** — Download the aeneas + charon binaries from the pinned GitHub release into `.aeneas/`, and install the Rust nightly `charon-driver` needs. Skips the download if the installed version already matches the pinned tag.
- **`npm run aeneas-extract`** — Run the extraction pipeline: apply the Rust translation patches → charon (Rust → LLBC) → revert the patches → aeneas (LLBC → Lean) → post-extraction tweaks. Refuses to run if the installed aeneas does not match the pinned tag.
- **`npm run patches-check`** — Check the translation patches: each applies on its own, all apply and revert in forward and reverse order, and the working tree is unchanged afterwards.

## Configuration

All extraction options live in `aeneas-config.yml` at the project root.

## Translation patches

The Rust sources (`src/`, `build.rs`, `Cargo.toml`) are kept identical to the upstream commit
named in `aeneas-config.yml`. Every change needed for the translation is a patch in
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

See `extraction.md` for the full procedure.

## Updating the aeneas version

The aeneas **release tag** is pinned only in `lakefile.toml` (`rev` in the aeneas `[[require]]`
block). The install and extract scripts read it from there. See `doc/aeneas.md`.
