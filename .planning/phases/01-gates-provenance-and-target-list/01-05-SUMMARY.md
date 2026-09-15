---
phase: 01-gates-provenance-and-target-list
plan: 05
type: execute
wave: 4
status: checkpoint-open
pr_boundary: A
pr_boundary_terminal: true
requirements: [INFRA-01, INFRA-03, PROV-01]
files_modified: []
lean_files_touched: 0
src_touched: false
srctranslated_touched: false
allowed_sorries: 0
measured: 2026-09-15
executed_by: orchestrator (inline; reporting plan, no worktree)
---

# 01-05 — PR A boundary report

Reporting plan. No files were modified, no branch was created, no pull request
was created, nothing was pushed. The only artifact is this SUMMARY.

Executed inline by the orchestrator rather than in an isolated worktree: this
plan's deliverable is a set of *measurements of the real repository*, and a
fresh worktree would have measured itself and needed another ~16 GB build to
re-run the gates. `files_modified` is empty, so there is nothing for isolation
to protect.

## PR A deliverables, against the requirements they discharge

| # | Deliverable | Requirement | From |
|---|-------------|-------------|------|
| 1 | `docs/ISSUE_TEMPLATE.md` rewritten as a per-property **PR** checklist; the phantom `#check_no_sorry` gate removed from `docs/rubrics/spqr-plan-review.md` and `CLAUDE.md` | INFRA-01 | 01-01 |
| 2 | `scripts/check-gates.sh` (five gates), `scripts/axiom-allowlist.txt` (20 entries), `scripts/check-provenance.py`, the `check-lint.sh` shim, the README gates section | INFRA-03, PROV-01 | 01-02, 01-04 |
| 3 | `docs/spqr-properties.md` `Source:` retrofit on all 42 rows, plus `docs/spec-sections.txt` (23 entries) and `docs/scka-refs.txt` (28 entries) transcribed from the two source PDFs | PROV-01 | 01-03 |
| 4 | The first real five-gate run, the CI cross-check, and nine negative controls | INFRA-03 | 01-04 |

## Gate colours — all five stated, including the red one

Measured on the merged tree at `8450d72` by the orchestrator, independently of
the executors' own reports.

| Gate | Scoped run | Notes |
|------|-----------|-------|
| 1 `lake build`, no non-sorry warning | **PASS** | Command lines byte-identical to `lean.yml:47,48,50`. Documented divergence: gate 1 keeps `pipefail` while dropping `errexit`, so a non-zero `lake build` is a local FAIL that CI's `run:` block cannot see |
| 2 `lake exe runLinter Spqr` | **PASS** | 01-04 found this could pass on a stale olean — `runLinter` builds the linter, not the library. Now reproduces CI's precondition when gate 1 is not in the run |
| 3a `lake env lean scripts/Audit.lean` | **PASS** | Turned out to be CI-comparable, which the plan did not anticipate; agrees with CI |
| 3b sorry-manifest delta | **PASS** | Local-only policy, no CI counterpart |
| 4 `#print axioms` vs allowlist | **PASS scoped / RED by default** | See below — this is the red one |
| 5 provenance over `Source:` citations | **PASS** | `every one of 42 row(s) has a resolving Source: citation`, exit 0. Zero `Unsourced` rows |

**Gate 4 is legitimately red on its default target set: 100 findings** — 82
non-allowlisted aeneas-generated stub axioms and 18 `sorryAx` specs. This is
not a defect and was deliberately not greened. `scripts/axiom-allowlist.txt` is
the trusted base; Phase 4 (AXIOM-01..06) owns it, and expanding it here to make
the gate green is a named threat (T-1-04). Both lists are queued in 01-04's
Deferred Issues. The scoped run
(`--axiom-target spqr.kdf.hkdf_to_slice_spec`) passes all six gate lines, exit 0.

`scripts/axiom-allowlist.txt` was touched in 01-04 but **comment-only**: 20
entries before, 20 after, no axiom added or removed. Verified by diff.

## Record commands, literal output

```
$ bash scripts/check-gates.sh --axiom-target spqr.kdf.hkdf_to_slice_spec
GATE 1: PASS
GATE 2: PASS
GATE 3a: PASS
GATE 3b: PASS
GATE 4: PASS
GATE 5: PASS
All selected gates PASS.
GATES_EXIT=0
```

```
$ git grep -nE 'check[_]no[_]sorry' -- ':!.planning'
exit=1          # no output — the phantom gate is gone from all tracked files outside .planning/
```

```
$ python3 scripts/check-provenance.py
§12 index rows:   38 (37 individual, 1 aggregate)
GATE 5 PASS: every one of 42 row(s) has a resolving Source: citation.
exit=0
```

```
$ git status --porcelain -- src SrcTranslated '*.lean'
                # empty — no working-tree residue
$ git diff --name-only d47083c..HEAD -- src
                # empty — the code freeze holds
```

```
$ git diff --stat origin/main...HEAD | tail -1
 52 files changed, 17794 insertions(+), 19 deletions(-)
```

**Plan-text defect found.** The plan specifies
`./scripts/check-gates.sh spqr.kdf.hkdf_to_slice_spec`. That form **exits 2
with usage** — the runner takes `--axiom-target`. This is the gate-list input
validation 01-02 added on purpose, so a malformed invocation cannot silently
run nothing and report success. The plan text is wrong, not the script; the
correct form is recorded above.

## The base-branch question, re-measured 2026-09-15

`origin/main` is `e8f6689`. It contains **none** of the files this phase edits:

```
absent on origin/main: docs/spqr-properties.md
absent on origin/main: .planning/           (all of it)
absent on origin/main: docs/ISSUE_TEMPLATE.md
absent on origin/main: scripts/check-gates.sh
```

PR A change set over the full `origin/main...HEAD` range: **52 files, 17,794
insertions, 19 deletions**. This includes the tracked `.planning/` artifacts —
`commit_docs: true` on this project, so the plan set and the SUMMARYs are real
PR scope. Re-measure before opening; the number grows with every planning commit.

**Lean/toolchain diff, re-measured — and it is not empty:**

```
$ git diff --name-only origin/main..HEAD -- '*.lean' lakefile.toml lean-toolchain lake-manifest.json
Spqr.lean
Spqr/Specs/Chain/Chain/EpochIdx.lean
Spqr/Specs/Chain/Chain/New.lean
Spqr/Specs/Encoding/Polynomial/PolyEncoder/IntoPb.lean
```

These are **upstream commits this branch does not have**, not Phase 1 edits.
Evidence, in three independent forms:

- `git rev-list --left-right --count origin/main...HEAD` → `2  43`. HEAD is 2
  commits *behind* main and 43 ahead.
- `Spqr/Specs/Chain/Chain/EpochIdx.lean` exists on `origin/main` and **not** on
  HEAD — a file this branch lacks cannot be something this branch edited.
- `git log --oneline d7cf202..HEAD -- '*.lean'` is **empty**: no Phase 1 commit
  touched any `.lean` file at all.

Nothing was "repaired" to make the earlier draft's empty-diff assertion true.

## Unanticipated finding — `la/spec-catalog` already has an open PR

This is not in the plan and it bears directly on both branch questions.

```
#45  la/spec-catalog -> main  "Revert Rust setup workaround in Aeneas workflow"
     state=OPEN  draft=true  updated=2026-09-14
     https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/45
```

PR #45 is open **right now**, with `la/spec-catalog` as its head and `main` as
its base, and it currently shows 8 files. GitHub permits only one open PR per
(head, base) pair, so **a second PR from `la/spec-catalog` → `main` cannot be
opened.** Pushing this branch would add all 43 commits of Phase 1 to PR #45 —
a pull request whose title is "Revert Rust setup workaround in Aeneas workflow".

The remote branch is stale: `origin/la/spec-catalog` is `1bcec6e`, and
`git rev-list --left-right --count origin/la/spec-catalog...HEAD` → `0  34`.
Zero behind, 34 ahead, so a plain push suffices and the `--force-with-lease`
note at `.planning/STATE.md:76` is confirmed stale — but a plain push is
exactly what would fold Phase 1 into #45.

So PR A needs either a new branch off this work, or a decision to repurpose
#45 (retitle and rescope it). That is a user decision; GSD will not move work
between branches or touch a pull request on its own.

## Refs

PR A implementation tip: `e680d23c4132eeee9e27c7bde5fd8d1998e522bf`
(`docs(01-04): summarise the first real gate run` — the last task commit of
PR A's implementation work)

Branch head at report time: `8450d72bb7228584976f4f1aac4fc94e60286936`
(`docs(phase-01): update tracking after wave 3`). The two SHAs differ: the
merge commits and the orchestrator's tracking commits land after the last task
commit, and the `01-05-SUMMARY.md` commit lands after *both*. The PR A range
must include all of them — use `<base>...HEAD` at push time, not the
implementation tip.

PR B head: *awaiting user ruling — 01-06's precondition, execution is stopped on it*
PR B base: *awaiting user ruling — 01-09's range base*

These are two different refs. Recording one value for both would make
`<base>...HEAD` empty and would vacuously pass 01-09's change-set and
code-freeze checks.

## Verification

- [x] All four deliverables listed against their requirements
- [x] Literal output of the record commands carried above
- [x] All five gate colours stated, the red one named with its reason
- [x] Literal `PR A implementation tip:` line, later SUMMARY commit noted
- [ ] `PR B head:` / `PR B base:` — **open**, awaiting the user
- [x] `git log --oneline -1` shows no merge or PR-creation commit at tip
- [x] No `gh pr create`, `gh pr ready`, `gh pr edit` or `git push` was run
- [x] `git status --porcelain -- src SrcTranslated '*.lean'` empty
