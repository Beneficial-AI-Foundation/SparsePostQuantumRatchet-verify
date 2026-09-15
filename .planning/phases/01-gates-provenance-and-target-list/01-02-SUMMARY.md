---
phase: 01-gates-provenance-and-target-list
plan: 02
subsystem: infra
tags: [bash, python, lean, lake, gates, provenance, axiom-audit, ci-parity]

requires:
  - phase: (none)
    provides: existing scripts/check-lint.sh, scripts/Audit.lean, scripts/sorry-diff.py and .github/workflows/lean.yml, all read-only inputs
provides:
  - scripts/check-gates.sh - one command running all five gates with a fail accumulator and a per-gate PASS/FAIL/SKIP verdict
  - scripts/axiom-allowlist.txt - the 20-name gate-4 trusted base (3 builtins + 17 documented stubs), each stub with a file:line citation
  - scripts/check-provenance.py - gate 5, PROV-01 enforcement over docs/spqr-properties.md
  - scripts/check-lint.sh - a 3-line compatibility shim
  - scripts/README.md "Verification gates" documentation
affects: [01-03 (writes the Source: fields and the two reference lists gate 5 resolves against), 01-04 (first run of the build-dependent gates, measures the cold-run cost), 01-05 (reports gate status), Phase 4 AXIOM-01..06 (edits the allowlist)]

tech-stack:
  added: []
  patterns:
    - "Gate verdicts accumulate: every selected gate runs, SKIP counts as a failure, an unknown or empty --gates list is rejected"
    - "CI parity by byte-for-byte command copy, with intentional local strictness documented inline"
    - "Trusted base kept in a grep-able sidecar (scripts/axiom-allowlist.txt) so a change to it shows up as a diff"
    - "Fail-closed citation parsing: an unparseable form is a failure, never a skip"

key-files:
  created:
    - scripts/check-gates.sh
    - scripts/axiom-allowlist.txt
    - scripts/check-provenance.py
  modified:
    - scripts/check-lint.sh
    - scripts/README.md
    - .gitignore

key-decisions:
  - "Gate 4's target set defaults to every theorem/axiom declared under Spqr/Specs/** (463 today), overridable with repeatable --axiom-target; an empty target set reports SKIP, not PASS. The plan said targets arrive 'per argument' but named no source, and a gate with no targets is vacuous."
  - "Gate 1 keeps pipefail while dropping errexit, so a non-zero `lake build` is a local FAIL even though CI's run: block cannot see it. Documented inline as a deliberate divergence."
  - "Gate 4 splits into 4A (allowlist resolves against the tree, no build needed) and 4B (axiom closure, needs a build). Without lake, 4A still runs and 4B reports SKIP."
  - "Allowlist source validation uses a newline-tolerant `(?m)^(axiom|opaque)\\s+NAME` match with namespace-prefix stripping guarded by an `^namespace <prefix>$` check, rather than `^axiom +NAME`."
  - "Gate 5 checks ID-set agreement with the §12 index plus a 37-entry non-deviation floor, never count equality."

patterns-established:
  - "Negative controls before first real run: 12 synthetic gate-4 logs and 17 synthetic gate-5 citations were run through the real code paths using a stubbed `lake` and temporary catalogs"
  - "SKIP is a failure: no gate can report PASS without having run"

requirements-completed: [INFRA-03, PROV-01]

duration: 52min
completed: 2026-09-15
---

# Phase 01 Plan 02: Five-Gate Local Runner Summary

**One command (`scripts/check-gates.sh`) now runs all five repository gates with a fail accumulator; gate 4 cannot be fooled by a typo, a missing report, a wrapped axiom list or an unterminated bracket, and gate 5 enumerates all 42 catalog rows and currently fails on every one of them for want of a `Source:` field.**

## Performance

- **Duration:** ~52 min
- **Started:** 2026-09-15T00:00:00Z (worktree spawn)
- **Completed:** 2026-09-15
- **Tasks:** 3 of 3
- **Files created:** 3 — **modified:** 3

## Accomplishments

### Task 1 — gates 1-3, the shim and the gitignore entries (`b121921`)

`scripts/check-gates.sh` (`set -euo pipefail`, `LEAN_ABORT_ON_PANIC=1`) with
`--help`, `--gates`, `--allow-sorry`, `--axiom-target`, `--allowlist`,
`--baseline-ref`, `--baseline-dir`, `--skip-baseline`/`--no-delta` and
`--refresh-baseline`. Every selected gate runs, each prints
`GATE n: PASS|FAIL|SKIP`, and the script exits non-zero if any is not `PASS`.

`scripts/check-lint.sh` is now 3 lines and `exec`s `check-gates.sh --gates 1,2`.
`.gitignore` gained `.gate-cache/` and `.sorry-delta-comment.md`, appended at the
end of the "Local / generated" block with no reordering.

### Task 2 — gate 4 (`553acef`)

`scripts/axiom-allowlist.txt` holds exactly 20 names. Gate 4A validates them
against the tree; gate 4B elaborates one `#print axioms` per target in a
`mktemp -d` scratch file removed by a `trap`.

### Task 3 — gate 5 (`a906c12`)

`scripts/check-provenance.py` (standard library only: `argparse`, `pathlib`,
`re`, `sys`) plus the `## Verification gates` section of `scripts/README.md`.

## Gates 1 and 2 are byte-for-byte CI

Both sides of every command and filter line, diffed programmatically:

| `lean.yml` | text | identical in `check-gates.sh` |
|---|---|---|
| `:47` | `lake build --no-ansi 2>&1 \| tee /tmp/lake-build.log` | yes |
| `:48` | `if grep 'warning:' /tmp/lake-build.log \| grep -qv 'declaration uses .sorry'; then` | yes |
| `:50` | `grep 'warning:' /tmp/lake-build.log \| grep -v 'declaration uses .sorry'` | yes |
| `:57` | `lake exe runLinter Spqr 2>&1 \| tee /tmp/lake-lint.log \|\| true` | yes |
| `:58` | `if grep -q 'error:' /tmp/lake-lint.log; then` | yes |
| `:60` | `grep 'error:' /tmp/lake-lint.log` | yes |

The programmatic diff reported `identical_to_CI=True` and
`present_in_runner=True` for all six.

**One deliberate divergence, documented in a code comment at the gate:** a
GitHub `run:` block runs under `bash -e` with no `pipefail`, so CI's
`lake build … | tee …` reports `tee`'s status and a failing `lake build` is
invisible there. Gate 1 drops `errexit` but keeps `pipefail`, so `build_rc` is
`lake`'s status; a non-zero `lake build` is a local `FAIL`, and the warning
filter still runs either way (the plan's "a `lake` invocation that itself exits
non-zero is a FAIL, not a reason to skip the grep"). Gate 3b is likewise
stricter than CI, which reports the delta without failing.

## Gate 3b never reads the stale manifest

`sorry-manifest.txt` appears 5 times in `check-gates.sh`. The only paths used as
a **baseline** are `"$CACHE_DIR/sorry-manifest-$base_sha.txt"` and the copy taken
from `"$BASELINE_DIR/sorry-manifest.txt"` inside the freshly built baseline
worktree. The head side is `"$REPO_ROOT/sorry-manifest.txt"`, which gate 3a
regenerates in the same run and which gate 3b refuses to use if gate 3a did not
produce it (`skip 3b "no head manifest; gate 3a must run first"`). The repo-root
file is never compared against itself and never used as the base. Keying the
cache by `git rev-parse origin/main` makes it self-invalidate when the ref moves,
the same shape as CI's `sorry-manifest-main-${{ github.sha }}`.

## Gate 4: allowlist, and the assertions that make it non-vacuous

**The 20 names.** 3 builtins (`propext`, `Classical.choice`, `Quot.sound`,
matching `Audit.lean:26-27`) plus 17 stubs. `grep -vc '^\s*#\|^\s*$'` returns
`20`; `grep -c 'FunsExternal.lean:'` returns `18`, so every stub carries its
citation. All three traps respected:

1. `FunsExternal.lean` has `open spqr` at line 16, not `namespace spqr`, so the
   entries are root-level `libcrux_ml_kem.*`, `libcrux_hmac.*`, `encoding.*`,
   `incremental_mlkem768.*`. The one namespaced entry is
   `spqr.kdf.hkdf_to_slice_spec`.
2. The `opaque` declarations are documented in a `#` comment as invisible to
   `#print axioms`, not listed. The HMAC wrapper is referred to descriptively so
   that `grep -q 'HMAC_SHA256' scripts/axiom-allowlist.txt` exits 1, as the
   acceptance criterion requires.
3. The bare root-level `axiom initial_state` (`:3694`), `send` (`:3700`) and
   `recv` (`:3708`) are called out as dead aeneas template leftovers and are not
   allowlisted; `grep -qE '^(initial_state|send|recv)\s*$'` exits 1.

**The multiline declaration is accepted by name.** 4A's accept line, verbatim
from the run:

```
  accept incremental_mlkem768.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275  (SrcTranslated/FunsExternal.lean:3687-3688)
```

The reported span `3687-3688` is the keyword line and the name line, confirming
the wrap. 119 `^axiom$`-alone lines exist in that file (measured), so a
`^axiom +NAME` matcher would have rejected a correct, mandatory entry. The
matcher used is `(?m)^(?:axiom|opaque)\s+NAME(?![\w.])` over the whole file text
(`\s` spans the newline), with namespace-prefix stripping guarded by an
`^namespace <prefix>$` check in the same file — which is how
`spqr.kdf.hkdf_to_slice_spec` resolves to
`Spqr/Specs/Kdf/HkdfToSlice.lean:25`. All 20 entries resolve.

**The assertion that rejects a target with no report line.** In
`parse_axiom_report`:

```python
for t in targets:
    if t not in reports:
        failures.append(f"no #print axioms report for target '{t}' "
                        "(target missing, renamed or the elaboration aborted)")
```

Every target is asserted **by name** against the set of parsed report headers,
so a typo'd or renamed target cannot pass vacuously even if Lean emitted no
error the log-scanner recognised.

**Negative controls, all run through the real code path** with a stubbed `lake`
feeding a canned `#print axioms` log (plan 01-04 owns the real-build run):

| Control | Verdict |
|---|---|
| clean: one `depends on axioms: [...]`, one `does not depend on any axioms` | PASS |
| axiom list wrapped across 3 lines, all allowlisted | PASS |
| wrapped list whose 3rd line hides the non-allowlisted `send` | FAIL — `'A' depends on non-allowlisted axiom(s): send` |
| `unknown identifier 'Afoo'` | FAIL (2 findings: the error line and the missing report) |
| `unknown constant 'Afoo'` | FAIL (same) |
| two targets, only one report | FAIL — `no #print axioms report for target 'B'` |
| `[propext,` then EOF | FAIL — `malformed #print axioms report for 'A': no closing ']' before the next report or EOF` |
| `[propext,` then the next report header | FAIL — same malformed message |
| `sorryAx` with no opt-in | FAIL |
| `sorryAx` with `--allow-sorry A` | PASS |
| a non-allowlisted axiom `my.new.axiom` | FAIL |
| clean reports but `lake env lean` exited 1 | FAIL — `lake env lean exited 1 on the scratch file` |

Scratch files live under `mktemp -d` (mode 0700) with `trap 'rm -rf …' RETURN`
(threat T-1-14).

## Gate 5: registry, index agreement, and proof that it is not vacuous

Full output of `python3 scripts/check-provenance.py` on the unchanged catalog
(head and tail; the middle is the same `no \`Source:\` field` line for every
remaining row):

```
Registry entries: 42 (37 non-deviation, 5 deviation)
§12 index rows:   38 (37 individual, 1 aggregate)
The two numbers are not expected to be equal: §12 collapses D1-D5 into one aggregate entry.  ID-set agreement is what is checked.
note: docs/spec-sections.txt does not exist; every `Spec §x.y` citation will fail (plan 01-03 transcribes it)
note: docs/scka-refs.txt does not exist; every `SCKA Def./Fig. n` citation will fail (plan 01-03 transcribes it)

Citation failures (42) in 42 row(s):
  ID          WHERE                        REASON
  D1          §11 table (line 435)         no `Source:` field
  ...
  PROP-9      §10 table (line 412)         no `Source:` field

GATE 5 FAIL: 0 structural, 42 citation failure(s).
```

Exit status 1, and `GATE 5: FAIL (unresolved Source: citations or §12 index
disagreement)` through the runner. **Both numbers as the plan predicted: 42
registry entries against 38 index rows, symmetric difference empty (0 structural
failures) once D1–D5 is mapped to its aggregate entry.** The figure 39 appears
nowhere and is neither count. The 42 breaks down as 28 `###` headings + 9 §10
rows + 5 §11 deviation rows.

Structural checks, exercised on synthetic catalogs:

| Control | Verdict |
|---|---|
| a `Source` **column** in a §10-style table | read correctly; `PROP-9` passed on `src/chain.rs:350-368` |
| `D1` in both §11 tables (5-column + Decision/Status) | **one** registry entry, joined by ID |
| a registry row absent from the §12 index | FAIL — `PROP-10 is a catalog row but is absent from the §12 index` |
| an index ID with no registry row | FAIL — `PROP-77 is in the §12 index but no catalog row was enumerated for it` |
| a registry with 2 non-deviation entries | FAIL — `below the floor of 37 - enumeration is incomplete` |

Citation-form controls, one recorded example per form:

| Citation | Verdict |
|---|---|
| `src/lib.rs:212-236` | PASS |
| `src/chain.rs:350` | PASS |
| `src/does-not-exist.rs:1-2` | FAIL — `no such file 'src/does-not-exist.rs'` |
| `src/lib.rs:99999` | FAIL — `'src/lib.rs' has 1175 lines; citation reaches line 99999` |
| `src/lib.rs:300-200` | FAIL — `is not a line range` |
| `Spqr/Specs/Kdf/HkdfToSlice.lean:25` | FAIL — `unparseable citation … (a Spqr/Specs path belongs on an Evidence: line)` |
| `Unsourced - no spec ground found` | FAIL — `marked Unsourced (…)` |
| `Spec §2.5` with no `docs/spec-sections.txt` | FAIL — `cannot resolve … does not exist (plan 01-03 transcribes it)` |
| `SCKA Def. 3.1` with no `docs/scka-refs.txt` | FAIL — same shape |
| `Spec §2.5` with the list present | PASS |
| `Spec §99.99` with the list present | FAIL — `unknown ML-KEM Braid section '§99.99'` |
| `SCKA Def. 3.1`, `SCKA Fig. 2` with the list present | PASS |
| `SCKA Fig. 16` with the list present | FAIL — `unknown SCKA reference 'Fig. 16'` |
| `Spec §2.5; src/lib.rs:1-3` (both good) | PASS |
| `Spec §2.5; src/lib.rs:1-9` (one bad) | FAIL on the bad one — one good citation does not rescue the list |
| `src/lib.rs:212-236; src/nope.rs:1` | FAIL on `src/nope.rs` |

`--gates 5` on this unbuilt tree exits 1 and its output contains **zero**
occurrences of the string `lake`, so gate 5 truly needs no build. `--help` exits
0 and lists all five gates. No package was installed; the checker imports only
`__future__`, `argparse`, `pathlib`, `re`, `sys`.

## Nothing the gates check was modified

- `git diff --quiet -- .github/workflows scripts/Audit.lean scripts/sorry-diff.py` exits **0** (threat T-1-17).
- `git status --porcelain -- src SrcTranslated '*.lean'` is **empty** — zero `.lean`, `src/` or `SrcTranslated/` hunks, matching `allowed_sorries: 0` and `lean_files_touched: 0`.
- `git diff .gitignore` is two added lines and no reordering.
- `docs/ISSUE_TEMPLATE.md`, `docs/rubrics/spqr-plan-review.md` and `CLAUDE.md` — owned by the concurrent plan 01-01 — were not touched.

## Deviations from Plan

### Auto-fixed issues

**1. [Rule 2 — missing critical functionality] `--gates` accepted an unknown gate number and reported a vacuous success**

- **Found during:** Task 1, smoke-testing the flag parser
- **Issue:** `./scripts/check-gates.sh --gates 9` ran no gate, printed
  `All selected gates PASS` and exited **0**. That is exactly threat T-1-01 —
  a gate run that reports PASS without checking anything — reachable by a typo.
- **Fix:** the gate list is validated against `1 2 3 4 5` before any gate runs
  (exit 2 on an unknown or empty entry), and a second backstop refuses to
  report success when no gate produced a verdict at all
  (`no gate produced a verdict - refusing to report success`, exit 1).
- **Files modified:** `scripts/check-gates.sh`
- **Commit:** `b121921`

**2. [Rule 3 — blocking issue] `selected N && gate_N` aborted the script under `errexit`**

- **Found during:** Task 1
- **Issue:** with `set -e`, a top-level `selected 1 && gate_1` whose left side
  returns non-zero fails the whole AND-list and kills the script, so
  `--gates 5` alone would have exited before reaching gate 5.
- **Fix:** rewritten as `if selected N; then gate_N; fi`.
- **Files modified:** `scripts/check-gates.sh`
- **Commit:** `b121921`

### Decisions the plan left open

**3. Gate 4's default target set.** The plan specifies "one
`#print axioms <name>` per argument" but names no source for the arguments, and
`files_modified` does not allow a new target-list file. Resolved without adding
a file: `--axiom-target` (repeatable) supplies targets explicitly, and with none
given gate 4 derives them from every `theorem`/`lemma`/`axiom` declared under
`Spqr/Specs/**` with namespace tracking — **463 targets** today. An empty
derived set reports `SKIP`, never `PASS`. Plan 01-04, which owns the first real
run, can narrow the set with `--axiom-target` if 463 elaborations prove too
slow.

**4. `--skip-baseline` semantics.** `01-RESEARCH.md` wanted a partial run to
stay useful; the plan requires SKIP to count as a failure. Both honoured:
`--skip-baseline` still runs and reports gates 1, 2, 3a, 4 and 5, and gate 3b
prints `SKIP (--skip-baseline given; no delta computed)` which makes the overall
exit non-zero.

### Deliberate non-divergences

`shellcheck` was **not** installed (`command -v shellcheck` → not found);
`bash -n` plus a careful read was the fallback, as the plan directs. No package
manager ran.

## Deferred / known-red

- Gate 5 is **known red** and will stay red until plan 01-03 adds the `Source:`
  fields and transcribes `docs/spec-sections.txt` and `docs/scka-refs.txt`.
  That is the intended state: its first recorded output being a FAIL is the
  T-1-01 mitigation.
- Gates 1, 2, 3a, 3b and 4B have **not been run against a real build** — the
  tree is unbuilt and a cold `lake build` is a GB-scale download plus tens of
  minutes. The plan explicitly assigns the first real run, the CI cross-check on
  `origin/main` and the cold-run cost measurement to plan 01-04, which also
  fills in the `Measured cold-run cost: TBD` line in `scripts/README.md`.
- `scripts/nolints.json` and the `lake exe cache get` step inside the baseline
  build are unverified for the same reason.

## Threat Flags

None. No network endpoint, auth path or schema was added; the new code reads
repository files and shells out to `lake`, `git` and `python3` only. `mktemp -d`
plus a `trap` covers T-1-14; `git worktree remove --force` is documented as the
teardown so no `rm -rf` of a live worktree is suggested.

## Self-Check: PASSED

Created files present:

- `FOUND: scripts/check-gates.sh`
- `FOUND: scripts/axiom-allowlist.txt`
- `FOUND: scripts/check-provenance.py`

Commits present in `git log`:

- `FOUND: b121921` — feat(01-02): add five-gate local runner with gates 1-3
- `FOUND: 553acef` — feat(01-02): add gate 4 axiom allowlist and a wrap-aware, typo-proof matcher
- `FOUND: a906c12` — feat(01-02): add gate 5 provenance checker and document all five gates

Plan-level `<verification>` block, all seven items:

1. `bash -n scripts/check-gates.sh` and `bash -n scripts/check-lint.sh` — **pass**
2. `ast.parse` of `scripts/check-provenance.py` — **pass**
3. `./scripts/check-gates.sh --help` — exit **0**, lists all five gates
4. `./scripts/check-gates.sh --gates 5` — exit **1**, zero `lake` invocations
5. `grep -vc '^\s*#\|^\s*$' scripts/axiom-allowlist.txt` — **20**
6. `git diff --quiet -- .github/workflows scripts/Audit.lean scripts/sorry-diff.py` — exit **0**
7. `git status --porcelain -- src SrcTranslated '*.lean'` — **empty**
