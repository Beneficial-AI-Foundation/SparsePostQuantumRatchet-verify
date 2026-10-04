# Updating Aeneas

This repo consumes Aeneas from a single **GitHub release tag**, used in two places that must stay
in sync:

1. `aeneas-config.yml` (`aeneas.tag`): the release whose Charon + Aeneas **binaries** are downloaded
   by `npm run aeneas-install` into `.aeneas/`. These produce the extraction (`SrcTranslated/*`,
   `translation.json`).
2. `lakefile.toml` (`[[require]] name = "aeneas"`, `rev`): the Aeneas **Lean library** our specs are
   checked against.

## Procedure

```bash
# 1. Pick a release.
gh release list -R AeneasVerif/aeneas

# 2. Set the same tag in both places:
#      - aeneas-config.yml :  aeneas.tag: "<tag>"
#      - lakefile.toml     :  rev = "<tag>" (under [[require]] name = "aeneas")

# 3. Refresh `lake-manifest.json`.
lake update aeneas

# 4. Download the Charon + Aeneas binaries for the new tag.
npm run aeneas-install

# 5. Re-extract: Charon -> Aeneas -> tweaks.
npm run aeneas-extract

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
