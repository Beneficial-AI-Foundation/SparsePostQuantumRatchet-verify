---
phase: 01-gates-provenance-and-target-list
plan: 04
subsystem: infra
tags: [lean, lake, gates, axiom-audit, ci-parity, negative-controls, cold-build]

requires:
  - phase: 01-gates-provenance-and-target-list
    provides: "01-02's scripts/check-gates.sh, scripts/axiom-allowlist.txt and scripts/check-provenance.py - written but never run against a build"
  - phase: 01-gates-provenance-and-target-list
    provides: "01-03's Source: retrofit and the two reference lists, without which gate 5 is red for a reason unrelated to the script"
provides:
  - "a gate-4 matcher written against the observed Lean 4.31.0 #print axioms output, not against an assumption"
  - "a gate-4 default target set every member of which #print axioms can address (393, was 463 with 70 unresolvable)"
  - "gate 2 no longer able to pass on a stale olean when run without gate 1"
  - "the measured cold-run cost in scripts/README.md, with the mathlib-cache caveat"
  - "a nine-row negative-control matrix with literal output: five gates observed failing, one observed passing where it must"
  - "a built working tree (.lake) and a built origin/main baseline worktree with its manifest cached at the SHA-keyed path"
affects:
  - "01-05 (reports gate status; gate 4's default run is red on 100 real findings)"
  - "Phase 4 AXIOM-01..06 (owns the allowlist and the --allow-sorry set; 100 findings are queued for it)"

tech-stack:
  added: []
  patterns:
    - "Settle an output format by elaboration probe and paste the literal result, rather than matching on remembered wording"
    - "A negative control is only met when the observed output is recorded; a PASS is the failure condition for eight of the nine rows"
    - "Fix the tooling that produces spurious findings; never edit the trusted base to turn a real finding green"
    - "Reproduce CI's precondition locally when a gate is run in isolation, without altering the CI-identical command"

key-files:
  created: []
  modified:
    - scripts/check-gates.sh
    - scripts/axiom-allowlist.txt
    - scripts/README.md
    - .planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md

key-decisions:
  - "Gate 4's routine invocation is the scoped `--axiom-target` form. The default 393-target run is left RED on 100 genuine findings (82 non-allowlisted aeneas stub axioms, 18 sorryAx specs) rather than tuning scripts/axiom-allowlist.txt to green it - the allowlist is the trusted base and Phase 4 owns it."
  - "Research assumption A1 was wrong about unresolvable names: Lean 4.31.0 emits `Unknown constant` with a capital U and backticks, so 01-02's lower-case substring test never fired. Corrected to the observed string."
  - "A2 settled and its wording tightened: an `opaque` is a legal subject of `#print axioms` but never appears inside any closure, so no opaque name was added and the allowlist count stays at 20."
  - "Three target-collection/parsing defects were fixed because all three were fail-strict noise burying real findings; the fix was accepted only after proving it removed exactly the 70 unresolvable names and added none."
  - "wave_0_complete was NOT flipped to true. Four Wave 0 deliverables owned by 01-06/01-07 are absent from disk, so the flag would be a false claim; nyquist_compliant was flipped."

metrics:
  duration: ~75min
  tasks: 3
  completed: 2026-09-15
---

# Phase 01 Plan 04: First Real Gate Run Summary

**The five gates ran on a built tree for the first time and all five were made to fail on demand; settling `#print axioms` empirically found that gate 4's typo detection had never worked and that its default target set contained 70 names Lean cannot resolve, and the measured cold-run cost turned out to be ~12 minutes rather than the predicted hours.**

## Performance

- **Duration:** ~75 min wall clock, dominated by three cold `lake build`s (357 s + 340 s + 352 s)
- **Completed:** 2026-09-15
- **Tasks:** 3 of 3
- **Files modified:** 4 — **created:** 0

## Worktree provenance

HEAD was spawned at `main` (`e8f6689`) rather than at the dispatch base and was
corrected before any work, per the standing worktree-harness defect:

```
ACTUAL_BASE=d47083cd3abf2906229efa38ae2bfb1121498af0     (wrong)
git checkout -B worktree-agent-a34fde24bf66ad3c7 332c90a
HEAD now: 332c90aba6abd49c7c2e34de2dcbb7fa4633ebe2
```

**Confirmed: every commit below is based on `332c90a`**, which contains waves 1–2
(01-01's honest template/rubric/CLAUDE.md, 01-02's five-gate runner, 01-03's full
provenance retrofit).

## Commits

| Task | Commit | What |
|------|--------|------|
| 1 | `6052f4f` | gate 4 matched against the real `#print axioms` output |
| 2 | `59cd0c1` | gate 4's default target set made addressable |
| 3 | `3e7100c` | nine negative controls, the gate-2 staleness fix, the cost line |

---

## Task 1 — the five probes, verbatim

`lake env lean` on the built tree, Lean 4.31.0
(`leanprover/lean4:v4.31.0`, `Lean (version 4.31.0, x86_64-unknown-linux-gnu, commit
68218e876d2a38b1985b8590fff244a83c321783, Release)`). Scratch file under `mktemp -d`.

Probe file:

```lean
import Spqr
-- probe 1: the hand-written axiom
#print axioms spqr.kdf.hkdf_to_slice_spec
-- probe 2: the opaque (tests A2)
#print axioms spqr.kdf.hkdf_to_slice
-- probe 3: a sorry-tainted theorem (tests the sorryAx path)
#print axioms spqr.decode_state_spec
#print axioms Spqr.Aeneas.collect_default_bridge
-- probe 4: a deliberately misspelled name
#print axioms spqr.kdf.hkdf_to_slice_spce
-- probe 5: a theorem with a long axiom closure (default print width)
#print axioms spqr.incremental_mlkem768.generate_spec
#print axioms spqr.authenticator.Authenticator.mac_ct_spec
```

`lean_rc=1`. **stdout, unedited:**

```
'spqr.kdf.hkdf_to_slice_spec' depends on axioms: [propext, Quot.sound, spqr.kdf.hkdf_to_slice_spec]
'spqr.kdf.hkdf_to_slice' depends on axioms: [propext]
'spqr.decode_state_spec' depends on axioms: [propext,
 sorryAx,
 Quot.sound,
 prost.encoding.DecodeContext,
 prost.error.DecodeError,
 Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance,
 Shared0SliceU8.Insts.BytesBufBuf_implBuf.chunk,
 Shared0SliceU8.Insts.BytesBufBuf_implBuf.remaining,
 bytes.buf.uninit_slice.UninitSlice,
 prost.message.Message.decode.default,
 core.option.Option.Insts.CoreDefaultDefault.default]
'Spqr.Aeneas.collect_default_bridge' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
/tmp/tmp.T0E24vz2yK/Probe.lean:10:14: error(lean.unknownIdentifier): Unknown constant `spqr.kdf.hkdf_to_slice_spce`
'spqr.incremental_mlkem768.generate_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.from_seed_spec]
'spqr.authenticator.Authenticator.mac_ct_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 libcrux_hmac.hmac,
 libcrux_hmac.hmac_sha256_tag32_spec]
```

stderr was empty.

No probe produced the `does not depend on any axioms` shape — everything real
depends on at least `propext` — so two supplementary probes were added, because
the script matches on that string and on the unknown-name string and neither had
been observed. Second probe file and **its unedited stdout:**

```lean
import Spqr
theorem probe_no_axioms : (1 : Nat) = 1 := rfl
#print axioms probe_no_axioms
#print axioms ThisNameDoesNotExistAnywhere
#print axioms spqr.kdf.totally_bogus
```

```
'probe_no_axioms' does not depend on any axioms
/tmp/tmp.T0E24vz2yK/Probe2.lean:6:14: error(lean.unknownIdentifier): Unknown constant `ThisNameDoesNotExistAnywhere`
/tmp/tmp.T0E24vz2yK/Probe2.lean:8:14: error(lean.unknownIdentifier): Unknown constant `spqr.kdf.totally_bogus`
```

### What the probes settled

| Assumption | Verdict | Evidence |
|---|---|---|
| A1, shape `'<name>' depends on axioms: [...]` | **correct** | probe 1 |
| A1, shape `'<name>' does not depend on any axioms` | **correct** | probe 1b |
| A1, unknown name is `unknown identifier` / `unknown constant` | **WRONG** | probes 4, 4b, 4c: `error(lean.unknownIdentifier): Unknown constant \`x\`` — capital U, backticks |
| A2, `opaque` invisible to `#print axioms` | **correct in the load-bearing sense, wording tightened** | probe 2 |

**The A1 error was a live false-green.** 01-02's parser tested
`"unknown identifier" in line or "unknown constant" in line`. Against the three
real error lines, old matcher 0/3, new matcher 3/3, and it does not fire on
`prost.error.DecodeError`:

```
OLD=False NEW=False | prost.error.DecodeError,
OLD=False NEW=True  | …Probe.lean:10:14: error(lean.unknownIdentifier): Unknown constant `spqr.kdf.hkdf_to_slice_spce`
OLD=False NEW=True  | …Probe2.lean:6:14: error(lean.unknownIdentifier): Unknown constant `ThisNameDoesNotExistAnywhere`
OLD=False NEW=True  | …Probe2.lean:8:14: error(lean.unknownIdentifier): Unknown constant `spqr.kdf.totally_bogus`
```

Gate 4 still caught a typo, via its independent per-target "no report for this
target" assertion — belt and braces working as designed — but only one of the
two intended findings fired. Control 6 below shows both firing now.

**A2, precisely.** `spqr.kdf.hkdf_to_slice` is `opaque`, and `#print axioms`
*answers* for it rather than erroring: `depends on axioms: [propext]`, the closure
of its type. The opaque itself is absent from that list and from every other
closure — the axiom beside it reports `[propext, Quot.sound,
spqr.kdf.hkdf_to_slice_spec]`, itself and never the opaque. So **no opaque name
was added to the allowlist and its entry count stays at 20**
(`grep -vc '^\s*#\|^\s*$'` → `20`). The allowlist's trap-2 comment was reworded
from "never appear in `#print axioms`" to "never enter an axiom closure", with the
probe output quoted inline.

**A third finding, unprompted: axiom lists wrap at the default print width.**
`spqr.decode_state_spec`'s 11-element closure came back over 11 lines, one axiom
per continuation line, with no `set_option format.width`. 01-02's
accumulate-to-`]` loop therefore runs on every real invocation, not only under a
synthetic control — and control 8 below needed no forcing.

### Task 1 verification

```
lake/build: OK
version: OK
no 'verified in plan' promise: OK
pattern present: OK
allowlist entry count: 20
```

---

## Task 2 — cold cost, the end-to-end run, and CI

### Cold-run cost

Machine: Intel Core Ultra 9 185H, 22 threads, 62 GB RAM, NVMe SSD, Linux;
2026-09-15. Both worktrees started with **no `.lake` directory at all**.

| Step | `cache get` | `lake build` | `Audit.lean` | total | disk |
|---|---|---|---|---|---|
| working tree | 60 s | 297 s | — | **357 s** | 8.2 GB |
| `origin/main` (`e8f6689`) baseline worktree | 56 s | 270 s | 14 s | **340 s** | 8.1 GB |
| negative-control worktree (task 3) | — | 352 s | — | 352 s | ~8 GB |

~12 min and ~16 GB for the first full five-gate run from nothing; **19–41 s warm**.

**The number needs its caveat, and `scripts/README.md` carries it.** The
machine-level mathlib cache at `~/.cache/mathlib` was already populated (6.4 GB,
142 126 `.ltar` files), so nothing was downloaded:

```
Decompressing 8538 already-cached file(s) (4 already decompressed)
Using cache (Azure) from origin: (some leanprover-community/mathlib4)
No files to download
Decompressed 8538 already-cached file(s)
Completed successfully in 12066 ms!
```

So this is *cold worktree, warm machine*. Research's "tens of minutes on a warm
cache, hours without" was pessimistic for the warm case on 22 cores and remains
the right expectation for a genuinely cold machine, which must add the GB-scale
olean download to each row. A concurrent unrelated Lean process was running on
the machine throughout, so these are upper bounds.

### End-to-end run

The plan's literal command `./scripts/check-gates.sh spqr.kdf.hkdf_to_slice_spec`
cannot work — the script rejects positional arguments by design
(`unknown option`) — so the target was passed as `--axiom-target`, which is what
the flag exists for. Recorded as a deviation below.

```
./scripts/check-gates.sh \
  --baseline-dir /home/lacra/git_repos/baif/spqr-gate-baseline \
  --axiom-target spqr.kdf.hkdf_to_slice_spec
```

**Per-gate verdict, verbatim:**

```
=== SUMMARY ===
GATE 1: PASS
GATE 2: PASS
GATE 3a: PASS
GATE 3b: PASS
GATE 4: PASS
GATE 5: PASS

All selected gates PASS.
SCRIPT_EXIT=0 ELAPSED=19s
```

Supporting lines from the same run:

```
Using cached baseline manifest: …/.gate-cache/sorry-manifest-e8f66895d61acd0238abb8b2c656c423b381bd8a.txt
Allowlist entries: 20 (3 builtins)
Allowlist resolves against the tree.
Targets: 1
Targets checked: 1; reports parsed: 1
Every target's axiom closure is within the allowlist.
Registry entries: 42 (37 non-deviation, 5 deviation)
§12 index rows:   38 (37 individual, 1 aggregate)
GATE 5 PASS: every one of 42 row(s) has a resolving Source: citation.
```

Gate 1 saw 63 warnings, every one `declaration uses 'sorry'`; the non-sorry filter
found nothing. Gate 3a wrote a 146-declaration manifest. Gate 3b: `New in this PR
(all): 0`, `New in this PR (specs): 0`.

### The default target set is a different story

Run with no `--axiom-target`, gate 4 checks every theorem/axiom under
`Spqr/Specs/**`. First run:

```
Targets: 463
Targets checked: 463; reports parsed: 389
FAIL: 245 axiom violation(s):
```

| Category | Count |
|---|---|
| non-allowlisted axiom | 82 |
| no report for target | 75 |
| unresolved target name | 70 |
| sorryAx without `--allow-sorry` | 18 |

145 of the 245 were the same ~70 names counted twice — tooling noise burying 100
real findings. Diagnosed to three causes, each confirmed against the tree before
anything was changed:

1. **68 `private` declarations.** e.g. `SliceIterMapCollect.lean:65` is
   `private theorem iterToList_trans`. Lean mangles a private name to
   `_private.<Module>.0.<Name>`, so the source-order name is not a constant in an
   importing module.
2. **2 doc-comment prose lines.** `DecodeChunk.lean:73` reads ``theorem against
   `encode_chunk` can identify the varint block it produced. -/`` and
   `FromCompletePoints.lean:167` reads ``lemma for the iterator step, then
   resolves the `if pt.x.value != i as u16` comparison`` — both inside `/-- … -/`
   blocks, both parsed as declarations named `against` and `for`.
3. **5 names that cannot match their own report**: 4 prime-suffixed
   (`…poly_mul_spec'`, printed by Lean with two closing quotes, which
   `'([^']+)'` cannot match at all so the report is dropped) and 1 `_root_.`
   prefixed (Lean prints the constant without the marker, the collector was
   prefixing the namespace stack as well).

All three are **fail-strict** — none could ever have produced a false green — but
all three are defects, so all three were fixed. The fix was accepted only against
this check:

```
old=463 new=393 unresolved_from_run=70
added by the fix (must be 0): 0
removed by the fix: 70
IDENTICAL: exactly the 70 unresolvable names were removed, nothing else
```

After the fix: `Targets checked: 393; reports parsed: 393` — every target
accounted for, where it had been 389/463.

**Gate 4's default run remains FAIL, on 100 findings, all genuine:**

```
FAIL: 100 axiom violation(s):
  82  non-allowlisted axiom
  18  sorryAx (no --allow-sorry)
```

The 82 are aeneas-generated stub axioms outside catalog §1's documented trusted
base (`core.ops.range.RangeFull.…get_unchecked`, `Aeneas.Std.core.fmt.Formatter`,
`prost.*`, `bytes.buf.*`, `Shared0SliceU8.*`); `Audit.lean` independently reports
`Total custom axioms: 237`. The 18 are sorry-tainted specs with no
`--allow-sorry` policy yet. **`scripts/axiom-allowlist.txt` was not touched** —
it is the trusted base, Phase 4 (AXIOM-01..06) owns it, and editing it here is
precisely the false-green this phase exists to prevent (threat T-1-04).

### CI cross-check

Run identified by SHA, not by recency. `gh run list --workflow lean.yml --branch
main` is unreliable here — it returned nothing newer than 2026-09-01 — so all 200
recent runs were searched for the exact `headSha`:

```
exact headSha matches for origin/main: 1
  databaseId 34961367398, headSha e8f66895d61acd0238abb8b2c656c423b381bd8a,
  event push, branch main, conclusion success, 2026-09-15T11:05:06Z
```

`git rev-parse origin/main` = `e8f66895d61acd0238abb8b2c656c423b381bd8a`. **Equal.**

CI step conclusions for that run:

```
success | Build and check for non-sorry warnings
success | Lint hand-written code
skipped | Restore base sorry manifest
skipped | Prepare base manifest
success | Axiom audit and sorry manifest
success | Save sorry manifest to cache
skipped | Upload sorry manifests
```

Local side: the **working tree's** script invoked by absolute path with the
`origin/main` worktree as CWD, because `origin/main` has no `check-gates.sh`:

```
CWD=/home/lacra/git_repos/baif/spqr-gate-baseline
HEAD=e8f66895d61acd0238abb8b2c656c423b381bd8a
SCRIPT=…/agent-a34fde24bf66ad3c7/scripts/check-gates.sh
GATE 1: PASS
GATE 2: PASS
All selected gates PASS.
SCRIPT_EXIT=0
```

| Gate | Local on `e8f6689` | CI on `e8f6689` | Comparable? |
|---|---|---|---|
| 1 build warnings | PASS | success (`lean.yml:46`) | **yes — matches** |
| 2 lint | PASS | success (`lean.yml:56`) | **yes — matches** |
| 3a axiom audit | PASS (rc 0, 146-line manifest) | success (`lean.yml:74`) | **yes — matches** |
| 3b sorry delta | PASS | no verdict — `sorry-delta-comment.yml:43` does not set `SORRY_FAIL_ON_NEW`, and the manifest steps are PR-only and `skipped` on this push run | **no — local-only policy, deliberately stricter** |
| 4 `#print axioms` | PASS scoped / FAIL default | no counterpart — CI has no `#print axioms` step | **no** |
| 5 provenance | PASS | no counterpart — CI has no provenance step | **no** |

No comparable gate disagreed, so nothing was adjusted. **Gate 3a turned out to be
comparable too**, which the plan did not anticipate: its command is byte-identical
to `lean.yml:74`. Recorded as a deviation.

One CI-parity caveat stands as 01-02 documented it: gate 1 keeps `pipefail` while
CI's `run:` block cannot see a non-zero `lake build`, so a build failure is a
local FAIL and a CI blind spot. It did not bite here — the build succeeded on both
sides.

### Task 2 verification

```
baseline manifest at SHA path: OK
no .sorry-delta-comment.md: OK
```

---

## Task 3 — nine negative controls

All run in a throwaway worktree `/home/lacra/git_repos/baif/spqr-negctl`
(detached at `59cd0c1`), removed with `git worktree remove --force` before this
summary was written. `STASH_BASELINE=5`, recorded before the first control.
**Nothing was ever parked in a stash and no pre-existing stash was touched.**

| # | Gate | What was changed | Expected | Observed | Verdict |
|---|------|------------------|----------|----------|---------|
| 1 | 1 | `Spqr/Specs/NegCtl/Warn.lean` binds `(n : Nat)` and never uses it; imported from `Spqr.lean` | FAIL, warning printed | `warning: Spqr/Specs/NegCtl/Warn.lean:12:32: Variable name \`n\` is not explicitly referenced.` → `GATE 1: FAIL (non-sorry build warnings)`, exit 1 | **met** |
| 2 | 2 | same module declares `Spqr.NegCtl.NegCtl` (`dupNamespace`) | FAIL with an `error:` line | `…Warn.lean:11:1: error: Spqr.NegCtl.NegCtl The namespace NegCtl is duplicated in the name` → `GATE 2: FAIL (runLinter reported error:)`, exit 1. Same run: `GATE 1: PASS` | **met** (after a fix, below) |
| 3 | 3a | `scripts/Audit.lean:23` → `import SpqrModuleThatDoesNotExist` | FAIL, **not** SKIP | `scripts/Audit.lean:23:0: error: unknown module prefix 'SpqrModuleThatDoesNotExist'` → `GATE 3a: FAIL (Audit.lean exited 1)`, `GATE 3b: SKIP (gate 3a did not produce a manifest)`, exit 1 | **met** |
| 4 | 3b | `theorem negctl_exported_sorry : (1 : Nat) = 1 := by sorry` in a module **imported** from `Spqr.lean` | FAIL naming the new line | `New in this PR (specs): 1`, `⚠ [Spqr.Specs.NegCtl.SorryExported] Spqr.Specs.NegCtl.negctl_exported_sorry (direct)`, `::error::1 new sorry-tainted declaration(s) in specs` → `GATE 3b: FAIL (new sorry-tainted declarations in Spqr.Specs.*)`, exit 1 | **met** |
| 5 | 3b | the identical theorem in a module **not** imported from `Spqr.lean` | **PASS** — the blind spot | `New in this PR (specs): 0`, `✓ No new sorry-tainted declarations in hand-written specs.` → `GATE 3b: PASS`, exit 0. `grep -c negctl_exported_sorry sorry-manifest.txt` → `0`, **while `SorryExported.olean` was present on disk** | **met (passes, as required)** |
| 6 | 4 | `--axiom-target spqr.kdf.hkdf_to_slice_spce` | FAIL with the unknown-name error, not a vacuous pass | `Targets checked: 1; reports parsed: 0`, `FAIL: 2 axiom violation(s)`: `unresolved target name: …error(lean.unknownIdentifier): Unknown constant \`spqr.kdf.hkdf_to_slice_spce\`` **and** `no #print axioms report for target 'spqr.kdf.hkdf_to_slice_spce'` → `GATE 4: FAIL`, exit 1 | **met** |
| 7 | 4 | a `sorryAx` target, without then with `--allow-sorry` | FAIL then PASS | `Spqr.Aeneas.collect_default_bridge` without: `FAIL: 1 … depends on sorryAx (not permitted; pass --allow-sorry …)` → `GATE 4: FAIL`, exit 1. With `--allow-sorry`: `Every target's axiom closure is within the allowlist.` → `GATE 4: PASS`, exit 0 | **met, both recorded** |
| 8 | 4 | drop the **continuation-line** axiom `libcrux_hmac.hmac_sha256_tag32_spec` from the allowlist | FAIL naming it | see below | **met** |
| 9 | 5 | one catalog `Source:` corrupted four ways, one at a time | FAIL naming the row, four times | see below | **met, all four** |

### Control 8 in full — the list really was wrapped

Route used: **the natural default print width.** No `set_option format.width` was
needed; task 1 had already shown lists wrap unforced. Raw
`/tmp/lake-axioms.log` from the 8a run, line-numbered, which is the evidence that
the list spanned more than one line:

```
     1	'spqr.authenticator.Authenticator.mac_ct_spec' depends on axioms: [propext,
     2	 Classical.choice,
     3	 Quot.sound,
     4	 libcrux_hmac.hmac,
     5	 libcrux_hmac.hmac_sha256_tag32_spec]
```

`libcrux_hmac.hmac_sha256_tag32_spec` is on **continuation line 5**, four lines
below the header.

- **8a**, full 20-entry allowlist: `Every target's axiom closure is within the allowlist.` → `GATE 4: PASS`, exit 0.
- **8b**, that one continuation-line entry removed (`entries: full=20 reduced=19`):

```
Allowlist entries: 19 (3 builtins)
Targets checked: 1; reports parsed: 1
FAIL: 1 axiom violation(s):
  - 'spqr.authenticator.Authenticator.mac_ct_spec' depends on non-allowlisted axiom(s): libcrux_hmac.hmac_sha256_tag32_spec
GATE 4: FAIL (axiom closure violates the allowlist …)
```

exit 1. A line-oriented matcher would have passed 8b. This one names the axiom.
**The control is met and was not waived.**

### Control 9 in full — four corruptions of PROP-21

`docs/spqr-properties.md:122`, original
`Source: Spec §1.1; src/v1/chunked/states.rs:203-220; src/v1/chunked/states.rs:361-368`.
Each corruption applied alone, then reverted.

```
############ CONTROL 9a - nonexistent file
corrupted line 122: Source: Spec §1.1; src/v1/chunked/states_NOPE.rs:203-220
runner_exit=1
  PROP-21  §2 heading (line 118)        no such file 'src/v1/chunked/states_NOPE.rs'
GATE 5 FAIL: 0 structural, 1 citation failure(s).

############ CONTROL 9b - line range past end of file
corrupted line 122: Source: Spec §1.1; src/v1/chunked/states.rs:99203-99220
runner_exit=1
  PROP-21  §2 heading (line 118)        'src/v1/chunked/states.rs' has 533 lines; citation reaches line 99220
GATE 5 FAIL: 0 structural, 1 citation failure(s).

############ CONTROL 9c - spec section absent from spec-sections.txt
corrupted line 122: Source: Spec §99.99; src/v1/chunked/states.rs:203-220
runner_exit=1
  PROP-21  §2 heading (line 118)        unknown ML-KEM Braid section '§99.99' (not in docs/spec-sections.txt)
GATE 5 FAIL: 0 structural, 1 citation failure(s).

############ CONTROL 9d - unparseable form
corrupted line 122: Source: see the state machine somewhere
runner_exit=1
  PROP-21  §2 heading (line 118)        unparseable citation 'see the state machine somewhere' - expected 'Spec §x.y', 'SCKA Def./Fig. n' or 'src/path.rs:a[-b]' (a Spqr/Specs path belongs on an Evidence: line)
GATE 5 FAIL: 0 structural, 1 citation failure(s).

############ restored line 122:
Source: Spec §1.1; src/v1/chunked/states.rs:203-220; src/v1/chunked/states.rs:361-368
############ clean re-run:
runner_exit=0
GATE 5 PASS: every one of 42 row(s) has a resolving Source: citation.
```

Four distinct diagnoses, PROP-21 named every time, and the row restored to PASS.
Notably 9d fails rather than skipping — a typo buys no pass.

### Control 5, the blind spot, named

`scripts/Audit.lean` walks only modules reachable from the root `Spqr` module, so
a `sorry` in an unexported module is invisible to gate 3b. The sharpest form of
the evidence: in control 5 the module was **still compiled on disk**
(`SorryExported.olean` present, left from control 4's build) and the sorry was
still absent from `sorry-manifest.txt` — so this is not merely "the file was never
built", it is "the audit does not look there".

This is exactly why 01-01 put a re-export line in the per-property checklist,
**`docs/ISSUE_TEMPLATE.md:131`**:

> - [ ] The new module is re-exported from `Spqr.lean`. `scripts/Audit.lean` cannot see a
>       module that is not reachable from the root, so an unexported proof passes the audit
>       gate vacuously.

`Audit.lean:11` says the same in its own header. The checklist line is load-bearing,
not decorative.

### Teardown and main-tree cleanliness

```
=== worktree list ===
…/SparsePostQuantumRatchet-verify                          c21327d [la/spec-catalog]
…/.claude/worktrees/agent-a34fde24bf66ad3c7                3e7100c [worktree-agent-…] locked
/home/lacra/git_repos/baif/spqr-gate-baseline              e8f6689 (detached HEAD)
/home/lacra/git_repos/baif/spqr-pr340                      acee47a (detached HEAD)

ls -d /home/lacra/git_repos/baif/spqr-negctl
  → No such file or directory

git stash list | wc -l                                     → 5   (== STASH_BASELINE)
git status --porcelain -- '*.lean' Spqr SrcTranslated src docs
  → (empty)
grep -c 'Measured cold-run cost:' scripts/README.md        → 1
grep -c 'Measured cold-run cost: TBD' scripts/README.md    → 0
git worktree list | grep -cv 'spqr-gate-baseline\|spqr-pr340'  → 2
```

The scratch worktree was removed through git, never `rm -rf`; no branch lingered
(it was `--detach`). The last check reads **2** rather than 1 only because this
executor's own agent worktree is still present; from the orchestrator's
perspective, once it is removed, the count is 1. `spqr-gate-baseline` is retained
deliberately — it is the gate-3b baseline and its `.lake` saves the 340 s rebuild.

---

## Deviations from Plan

### Auto-fixed issues

**1. [Rule 1 — Bug] Gate 4's unknown-name matcher never fired**
- **Found during:** Task 1
- **Issue:** the parser tested for lower-case `unknown identifier` / `unknown constant`; Lean 4.31.0 emits `error(lean.unknownIdentifier): Unknown constant \`x\`` (capital U, backticks). 0 of 3 real error lines matched.
- **Fix:** case-insensitive `UNKNOWN_NAME` regex that also matches the error-code tag. 3 of 3 match, no false positive on `prost.error.DecodeError`.
- **Files:** `scripts/check-gates.sh` — **Commit:** `6052f4f`

**2. [Rule 1 — Bug] 70 of 463 gate-4 targets were unresolvable**
- **Found during:** Task 2
- **Issue:** the collector emitted 68 `private` declarations (name-mangled by Lean), 2 doc-comment prose lines, and mishandled 4 prime-suffixed plus 1 `_root_.`-prefixed name.
- **Fix:** skip `private`, track `/- … -/` depth, strip `_root_.`, and anchor the report-header regex on its literal tail instead of `[^']+`. Verified to remove exactly the 70 unresolvable names and add none; report coverage 389/463 → 393/393.
- **Files:** `scripts/check-gates.sh` — **Commit:** `59cd0c1`

**3. [Rule 2 — Missing critical functionality] Gate 2 could pass on a stale olean**
- **Found during:** Task 3, control 2
- **Issue:** `lake exe runLinter Spqr` builds the linter, not the library it lints. The `dupNamespace` breakage reported `Linting passed for Spqr.` and `GATE 2: PASS` until the library was rebuilt — threat T-1-01, a gate passing without checking. CI cannot hit it because its build step always precedes its lint step.
- **Fix:** when gate 2 runs without gate 1, bring the library up to date first. The CI-identical command and filters are untouched. Re-tested with a deliberately stale olean: `--gates 2` alone now reports FAIL.
- **Files:** `scripts/check-gates.sh` — **Commit:** `3e7100c`

### Plan-text corrections

**4. The plan's end-to-end command cannot run as written.** `./scripts/check-gates.sh spqr.kdf.hkdf_to_slice_spec` — also in `01-VALIDATION.md`'s per-task map — passes the theorem positionally, and the script rejects positional arguments by design (`unknown option '…'`, exit 2). Run as `--axiom-target spqr.kdf.hkdf_to_slice_spec`, which is what the flag is for. The validation map's expectation (`echo $?` → `0`) holds.

**5. Gate 3a is CI-comparable, which the plan did not allow for.** The plan said gates 1 and 2 are "directly comparable" and treated gate 3 as local-only. Gate 3a's command is byte-identical to `lean.yml:74` ("Axiom audit and sorry manifest"), which succeeded on the same SHA, and gate 3a passes locally on that SHA. Recorded as a third matching gate. Gate **3b** remains local-only, as the plan said.

**6. `gh run list --branch main` is unreliable here.** It returned nothing newer than 2026-09-01 and did not list the 2026-09-15 push run at all. The run was found by scanning 200 recent runs for the exact `headSha`. Anyone repeating this cross-check should match on `headSha`, not trust the branch filter.

**7. `wave_0_complete` was NOT flipped to `true`.** The plan's acceptance criterion makes "all nine controls recorded" the condition; that condition is met, but it is necessary rather than sufficient. Four Wave 0 deliverables are absent from disk — `docs/proof-targets.md`, `docs/rubrics/spqr-statement-review.md`, `.claude/skills/spqr-statement-review/SKILL.md` (01-06) and `docs/spec-review-log.md` (01-07) — so the flag would be a false claim of exactly the kind this phase exists to prevent. `nyquist_compliant` **was** flipped to `true`, the build-and-baseline Wave 0 checkbox ticked, and both decisions recorded in the frontmatter with their basis.

### Not fixed, deliberately

**8. Gate 4's default run is RED on 100 findings.** 82 non-allowlisted
aeneas-generated stub axioms and 18 `sorryAx`-tainted specs. These are facts about
the repository, not script defects: catalog §1's documented trusted base does not
cover what the hand-written specs actually depend on (`Audit.lean` independently
counts 237 custom axioms), and there is no `--allow-sorry` policy yet. **The
allowlist was not edited.** Phase 4 (AXIOM-01..06) owns both. Tuning the trusted
base to green a gate is threat T-1-04.

## Deferred Issues

Queued for Phase 4 (AXIOM-01..06), with the evidence already in hand:

1. **82 non-allowlisted axioms** across the 393 default gate-4 targets. Families: `core.ops.range.*.get_unchecked*`, `Aeneas.Std.core.fmt.Formatter`, `prost.encoding.*`, `prost.error.*`, `prost.message.*`, `bytes.buf.*`, `Shared0SliceU8.Insts.BytesBufBuf_implBuf.*`, `core.option.Option.Insts.CoreDefaultDefault.default`. Each needs an allowlist entry with a citation, or a reason it should not have one. Full list in `/tmp/lake-axioms.log` shape; reproducible with `./scripts/check-gates.sh --gates 4`.
2. **18 `sorryAx`-tainted specs** needing an explicit `--allow-sorry` set (AXIOM-04/AXIOM-05), including `Spqr.Aeneas.collect_default_bridge` (aeneas#1043) and `spqr.decode_state_spec` plus the prost-dependent encoder specs.
3. **Gate 3b's blind spot is structural**, not fixable by allowlisting: `Audit.lean` cannot see an unexported module. Currently mitigated only by the human checklist line at `docs/ISSUE_TEMPLATE.md:131`. A mechanical check that every `Spqr/Specs/**/*.lean` is imported by `Spqr.lean` would close it and is not in this phase's scope.

No `deferred-items.md` was written; these are recorded here and are all inside this repository's own roadmap rather than out-of-scope discoveries.

## Requirements satisfied

- **INFRA-03** — one command runs five gates with a per-gate verdict; every gate has now been observed failing; the verdict on `origin/main` agrees with CI for all three gates CI runs.
- **ROADMAP criterion 1** — met, with the caveat that gate 4's *default* target set is legitimately red and the scoped invocation is the green one.

## Threat Flags

None. The committed diff touches three files under `scripts/` and one planning
document. Zero `*.lean`, zero `src/`, zero `SrcTranslated/`, zero `docs/`, and
`allowed_sorries: 0` is respected — the two `sorry` declarations written during
task 3 existed only inside the throwaway worktree and were deleted with it.

## Self-Check

Files claimed, checked on disk:

- `scripts/check-gates.sh` — FOUND
- `scripts/axiom-allowlist.txt` — FOUND
- `scripts/README.md` — FOUND
- `.planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md` — FOUND

Commits claimed, checked in `git log`:

- `6052f4f` — FOUND
- `59cd0c1` — FOUND
- `3e7100c` — FOUND

## Self-Check: PASSED
