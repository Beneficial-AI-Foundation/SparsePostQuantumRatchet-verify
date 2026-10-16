# Updating Aeneas

This repo consumes Aeneas from a single **GitHub release tag**, pinned only in `lakefile.toml`
(`[[require]] name = "aeneas"`, `rev`). It is used for both:

1. the Aeneas **Lean library** our specs are checked against;
2. the Charon + Aeneas **binaries** that `npm run aeneas-install` downloads into `.aeneas/`, and
   that produce the extraction (`SrcTranslated/*`, `translation.json`). The install and extract
   scripts read the tag from `lakefile.toml`.

## Procedure

```bash
# 1. Pick a release.
gh release list -R AeneasVerif/aeneas

# 2. Set the tag in lakefile.toml:  rev = "<tag>" (under [[require]] name = "aeneas")

# 3. Refresh `lake-manifest.json`.
lake update aeneas

# 4. Download the Charon + Aeneas binaries for the new tag.
npm run aeneas-install

# 5. Re-extract: patches -> Charon -> revert patches -> Aeneas -> tweaks.
npm run aeneas-extract

# 5b. Compare the hand-written FunsExternal.lean / TypesExternal.lean with the regenerated
#     *_Template.lean files: a declaration that Aeneas now translates, or that the Aeneas library
#     now provides, must be removed from the hand-written file.

# 6. Typecheck the project and fix any breakage from the update.
lake build
```

Step 4 also installs the Rust nightly that the bundled `charon-driver` needs (named in the
bundle's `rust-toolchain`), and syncs `lean-toolchain` if the release uses a different one.

## Checking the olean cache is actually used

If Lake is compiling `Aeneas.*` from source, the `rev` is not resolving to a release:

```bash
rm -rf .lake/packages/aeneas
lake build 2>&1 | tee /tmp/build.log
grep -ci "Building Aeneas" /tmp/build.log   # expect 0
```

## Platform support

Release binaries exist only for linux x86_64, linux aarch64, and macOS aarch64.
