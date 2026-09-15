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

#### Gate 4: the `#print axioms` output shapes it parses

Settled by elaboration probe on the built tree under Lean 4.31.0 (plan 01-04
task 1), not from documentation. Verbatim, these are the four shapes:

```
'spqr.kdf.hkdf_to_slice_spec' depends on axioms: [propext, Quot.sound, spqr.kdf.hkdf_to_slice_spec]
'probe_no_axioms' does not depend on any axioms
'spqr.encoding.gf.unaccelerated.poly_mul_spec'' depends on axioms: [propext, Classical.choice, Quot.sound]
Probe.lean:10:14: error(lean.unknownIdentifier): Unknown constant `spqr.kdf.hkdf_to_slice_spce`
```

Four things a reader editing gate 4 needs to know:

- An unresolvable name comes back as **`Unknown constant` — capital U, name in
  backticks**, tagged `error(lean.unknownIdentifier)`. Not the lower-case
  `unknown identifier '<name>'` that a first guess assumes.
- A **prime-suffixed** name is printed with two closing quotes (third line
  above), so a `'([^']+)'` header pattern fails to match the line at all and
  silently drops the report. 4 of the 393 default targets are primed.
- Axiom lists **wrap at the default print width** with one axiom per
  continuation line — no `set_option format.width` needed to reproduce it. The
  11-element closure of `spqr.decode_state_spec` spans 11 lines. Any matcher
  must accumulate to the closing `]`.
- An `opaque` declaration is a legal *subject* of `#print axioms` (it answers,
  it does not error) but never appears *inside* any closure, so no `opaque` name
  belongs on the allowlist.

The default target set is every non-`private` theorem/lemma/axiom declared under
`Spqr/Specs/**` (393 today). `private` declarations are excluded because Lean
mangles their names to `_private.<Module>.0.<Name>`, which `#print axioms`
cannot resolve from an importing module. Narrow the set with repeatable
`--axiom-target`.

**Gate 4's default run is currently red, for real reasons**, so the routine
invocation is the scoped one:

```bash
./scripts/check-gates.sh --axiom-target spqr.kdf.hkdf_to_slice_spec
```

`./scripts/check-gates.sh` with no `--axiom-target` reports 100 findings across
the 393 targets: 82 aeneas-generated stub axioms that are not in the documented
trusted base (`core.ops.range.*`, `prost.*`, `bytes.buf.*`, `Aeneas.Std.core.fmt.Formatter`
and similar) and 18 `sorryAx`-tainted specs with no `--allow-sorry` policy yet.
Those are facts about the repository, not script defects; Phase 4
(AXIOM-01..06) owns both the allowlist and the `--allow-sorry` set. Do not
silence them by editing `scripts/axiom-allowlist.txt` — it is the trusted base.

Gates 1 and 2 issue the commands from `.github/workflows/lean.yml` (lines 47
and 57) byte-for-byte, with the same `grep` filters, so that a green local run
means a green CI run for those two. One deliberate difference: CI's `run:`
block has no `pipefail`, so a non-zero `lake build` is invisible there; locally
it is a `FAIL`. Gate 3b is also stricter than CI, which reports the sorry delta
without failing (`sorry-delta-comment.yml` does not set `SORRY_FAIL_ON_NEW`).

One addition, not a divergence: when gate 2 runs **without** gate 1, it first
brings the library up to date. `lake exe runLinter Spqr` builds the linter but
not the library it lints, so on a stale tree it reports `Linting passed` for
code that was never compiled. CI never sees this because its build step always
precedes its lint step; a local `--gates 2` would otherwise be a false green.

Verified against CI on 2026-09-15: run `34961367398` of `lean.yml`, whose
`headSha` `e8f66895d61acd0238abb8b2c656c423b381bd8a` equals `git rev-parse
origin/main`. Its "Build and check for non-sorry warnings", "Lint hand-written
code" and "Axiom audit and sorry manifest" steps all succeeded, and gates 1, 2
and 3a of this script, run against the same commit, all report `PASS`. Gate 3b
is local-only policy, and gates 4 and 5 have no CI counterpart.

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

### Measured cold-run cost

Measured cold-run cost: **~12 min wall clock and ~16 GB of disk** for the first
full five-gate run starting from a checkout with no `.lake` at all — 6 min for
the working tree and 6 min for the `origin/main` baseline worktree. Measured
2026-09-15 on an Intel Core Ultra 9 185H (22 threads), 62 GB RAM, NVMe SSD,
Linux; Lean 4.31.0.

| Step | `lake exe cache get` | `lake build --no-ansi` | `Audit.lean` | total | disk |
|------|---------------------|------------------------|--------------|-------|------|
| working tree, no `.lake` | 60 s | 297 s | — | **357 s** | 8.2 GB |
| `origin/main` baseline worktree, no `.lake` | 56 s | 270 s | 14 s | **340 s** | 8.1 GB |

Once both are built, a full five-gate re-run is **20–40 s** (gate 4 dominated by
one `lake env lean` elaboration of the scratch file: ~3 s for the 393-target
default set, since every target is a `#print axioms` on an already-built tree).

**Read the `cache get` column with care.** These 56–60 s include cloning all ten
dependency repos, but *not* a mathlib olean download: the machine-level cache at
`~/.cache/mathlib` was already populated (6.4 GB, 142 126 `.ltar` files), so
`lake exe cache get` reported

```
Decompressing 8538 already-cached file(s) (4 already decompressed)
Using cache (Azure) from origin: (some leanprover-community/mathlib4)
No files to download
```

On a machine that has never fetched mathlib, add the GB-scale download to each
row. Research's "tens of minutes on a warm cache, hours without" was pessimistic
for the warm case on 22 cores and remains the right expectation for the cold one.

The baseline worktree's `.lake` is worth keeping: `--refresh-baseline` after a
`origin/main` move then rebuilds only the changed modules rather than all 2 543.

## Configuration

All extraction options live in `aeneas-config.yml` at the project root.

## Updating the aeneas version

The aeneas **release tag** is pinned in two places that must be kept in sync:

1. `aeneas-config.yml` — `aeneas.tag` (used by the install/extract scripts for the binaries)
2. `lakefile.toml` — `rev` in the aeneas `[[require]]` block (used by Lake for the Lean backend dependency)
