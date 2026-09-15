# Scripts

## Commands

- **`npm run aeneas-install`** — Download the aeneas + charon binaries from the pinned GitHub release into `.aeneas/`, and install the Rust nightly `charon-driver` needs. Skips the download if the installed version already matches the pinned tag.
- **`npm run aeneas-extract`** — Run the extraction pipeline: charon (Rust → LLBC) → aeneas (LLBC → Lean) → post-extraction tweaks.
- **`npm run src-diff`** — Generate `src-modifications.diff` comparing local `src/` against the pinned upstream commit.

## Verification gates

`scripts/check-gates.sh` runs all five repository gates locally and prints one
verdict per gate. Every selected gate runs — the script accumulates failures
instead of bailing on the first one — and exits non-zero if any gate is not
`PASS`. **A gate that could not run prints `SKIP` and counts as a failure**, so
a partial run can never be mistaken for a green one.

`scripts/check-lint.sh` is kept as a compatibility shim; it execs
`check-gates.sh --gates 1,2`.

| Gate | What it checks | Needs a build? |
|------|----------------|----------------|
| 1 | `lake build --no-ansi` produces no warning other than `declaration uses 'sorry'` | yes |
| 2 | `lake exe runLinter Spqr` reports no `error:` in the hand-written library | yes |
| 3a | `lake env lean scripts/Audit.lean` exits 0 and writes `sorry-manifest.txt` | yes |
| 3b | the sorry delta against an `origin/main` baseline has no new `Spqr.Specs.*` entry | yes |
| 4 | the allowlist still resolves against the tree (4A) and every target's `#print axioms` closure is within `scripts/axiom-allowlist.txt` (4B) | 4A no, 4B yes |
| 5 | every `Source:` citation in `docs/spqr-properties.md` resolves (PROV-01) | no |

Gates 1 and 2 issue the commands from `.github/workflows/lean.yml` (lines 47
and 57) byte-for-byte, with the same `grep` filters, so that a green local run
means a green CI run for those two. One deliberate difference: CI's `run:`
block has no `pipefail`, so a non-zero `lake build` is invisible there; locally
it is a `FAIL`. Gate 3b is also stricter than CI, which reports the sorry delta
without failing (`sorry-delta-comment.yml` does not set `SORRY_FAIL_ON_NEW`).

### Flags

```
--gates LIST          comma-separated subset, e.g. --gates 1,2 (default 1,2,3,4,5)
                      an unknown or empty list is rejected rather than run as a no-op
--allow-sorry THM     permit `sorryAx` in THM's axiom closure (gate 4, repeatable)
--axiom-target THM    check THM in gate 4 (repeatable); with none given, gate 4
                      checks every theorem/axiom declared under Spqr/Specs/**
--allowlist FILE      gate-4 allowlist (default scripts/axiom-allowlist.txt)
--baseline-ref REF    ref for the gate-3b baseline (default origin/main)
--baseline-dir DIR    worktree path for the baseline build (default ../spqr-gate-baseline)
--skip-baseline       skip the baseline build; gate 3b reports SKIP (a failure)
--no-delta            alias for --skip-baseline
--refresh-baseline    rebuild the cached baseline manifest even if present
-h, --help            usage
```

`scripts/check-provenance.py` (gate 5) can be run on its own and takes
`--verbose`, `--row ID` and `--catalog PATH`. It needs no build and only the
Python standard library. It resolves `Spec §x.y` against `docs/spec-sections.txt`
and `SCKA Def./Fig. n` against `docs/scka-refs.txt` — the PDFs are gitignored
and never parsed — and resolves `src/path.rs:a-b` against the working tree. A
row's `Evidence:` line is not parsed and not gated. Anything unparseable is a
failure, not a skip.

### Environment variables

| Variable | Effect |
|----------|--------|
| `LEAN_ABORT_ON_PANIC` | exported as `1` by the runner, matching CI |
| `SPQR_BASELINE_REF` | same as `--baseline-ref` |
| `SPQR_BASELINE_WORKTREE` | same as `--baseline-dir` |
| `SPQR_GATE_CACHE` | cache directory (default `.gate-cache`) |
| `SPQR_AXIOM_ALLOWLIST` | same as `--allowlist` |

### `.gate-cache/` layout and teardown

```
.gate-cache/
  sorry-manifest-<origin/main sha>.txt   gate-3b baseline, keyed by commit
```

Keying by SHA means the cache self-invalidates when `origin/main` moves, the
same shape CI uses for its `sorry-manifest-main-${{ github.sha }}` key. The
baseline build itself lives in a **separate git worktree** outside the repo
(`../spqr-gate-baseline` by default) so its `.lake` survives between refreshes
and only changed modules rebuild.

`.gate-cache/` and `.sorry-delta-comment.md` are gitignored.

To tear the baseline down, remove the worktree through git — never `rm -rf` it,
which leaves a stale administrative entry in `.git/worktrees`:

```bash
git worktree remove --force ../spqr-gate-baseline
rm -rf .gate-cache
```

Measured cold-run cost: TBD (recorded in plan 01-04).

## Configuration

All extraction options live in `aeneas-config.yml` at the project root.

## Updating the aeneas version

The aeneas **release tag** is pinned in two places that must be kept in sync:

1. `aeneas-config.yml` — `aeneas.tag` (used by the install/extract scripts for the binaries)
2. `lakefile.toml` — `rev` in the aeneas `[[require]]` block (used by Lake for the Lean backend dependency)
