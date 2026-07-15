# Updating Aeneas

This repo depends on Aeneas in two places that must stay pinned to the same commit:

1. `aeneas-config.yml` (`aeneas.commit`): the commit used to build the Charon + Aeneas
   binaries (`npm run aeneas-install` clones both here and builds them).
   These binaries produce the extraction (`SrcTranslated/*`, `translation.json`).
2. `lakefile.toml` (`[[require]] name = "aeneas"`, `rev`): the Aeneas Lean library the
   extracted code and our specs are checked against.

## Procedure

```bash
# 1. Find the latest main commit.
git ls-remote https://github.com/AeneasVerif/aeneas.git refs/heads/main

# 2. Set both pins to that commit (short or full SHA):
#      - aeneas-config.yml :  aeneas.commit: "<sha>"
#      - lakefile.toml     :  rev = "<sha>"   (under [[require]] name = "aeneas")

# 3. Refresh `lake-manifest.json`.
lake update aeneas

# 4. Rebuild the Charon + Aeneas binaries at the new commit.
npm run aeneas-install

# 5. Re-extract: Charon -> Aeneas -> tweaks.
npm run aeneas-extract

# 6. Typecheck the project and fix any breakage from the update.
lake build
```
