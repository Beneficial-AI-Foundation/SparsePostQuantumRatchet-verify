---
phase: 1
slug: gates-issues-and-deviation-decisions
status: draft
nyquist_compliant: false
wave_0_complete: false
created: 2026-09-14
---

# Phase 1 — Validation Strategy

> Per-phase validation contract for feedback sampling during execution.
> Derived from `01-RESEARCH.md` § Validation Architecture.

This phase produces shell scripts and Markdown, not Lean theorems. **Validated** means each
deliverable was *executed or parsed*, not merely written.

**Token hygiene (research pitfall P-7):** the phantom gate token this phase removes is written
here as `<phantom>` and never literally, so that this file does not re-introduce the string that
criterion 1's scoped grep must not find. Substitute the literal token at run time.

---

## Test Infrastructure

| Property | Value |
|----------|-------|
| **Framework** | none — no test harness exists for repository tooling. Validation is command execution with asserted output. |
| **Config file** | none. `lakefile.toml` declares a `Tests` lean_lib, deliberately **not** in `defaultTargets`; it covers `#guard_msgs` linter tests and Plausible property tests, not shell scripts. |
| **Quick run command** | `bash -n scripts/check-gates.sh && bash -n scripts/create-property-issues.sh && git grep -n '<phantom>' -- ':!.planning'` (expect exit 1 / no output) |
| **Full suite command** | `./scripts/check-gates.sh <targets>` (all four gates, with baseline) + `./scripts/create-property-issues.sh` (dry-run, all IDs) |
| **Estimated runtime** | quick ~2 s; full suite dominated by `lake build` — minutes warm, **first run costs a cold `lake exe cache get` + full build of the `origin/main` worktree** (research B-5) |

---

## Sampling Rate

- **After every task commit:** `bash -n` on any touched script + the scoped `<phantom>` grep +
  the §11 parse check if `docs/spqr-properties.md` changed. Seconds.
- **After every plan wave / at each PR boundary (A and B):** full `./scripts/check-gates.sh`,
  issue-script dry-run over all IDs, and the complete requirement→validation table below.
- **Before `/gsd:verify-work`:** the negative-control matrix has been run once and its observed
  output pasted into the phase SUMMARY.
- **Max feedback latency:** 5 s for per-task checks; gate-script runs are build-bound and are
  deliberately not per-task.

---

## Per-Task Verification Map

Task IDs are assigned by the planner. Each row below is a requirement-level obligation that at
least one task must carry as an `<automated>` verify. The planner fills the Task ID column.

| Task ID | Plan | Wave | Requirement | Threat Ref | Secure Behavior | Test Type | Automated Command | File Exists | Status |
|---------|------|------|-------------|------------|-----------------|-----------|-------------------|-------------|--------|
| TBD | PR A | 1 | INFRA-01 | — | Template names four gates by command + a catalog-and-index line | grep assertion | `grep -c '^- \[ \] `lake' docs/ISSUE_TEMPLATE.md` ≥ 3; `grep -q 'print axioms' docs/ISSUE_TEMPLATE.md`; `grep -q '§12' docs/ISSUE_TEMPLATE.md` | ❌ W0 | ⬜ pending |
| TBD | PR A | 1 | INFRA-01 | — | No operative document cites a gate that does not exist | grep assertion | `git grep -n '<phantom>' -- ':!.planning'` exits 1 with no output | ❌ W0 | ⬜ pending |
| TBD | PR A | 1 | INFRA-03 | — | Gate script is syntactically valid | static | `bash -n scripts/check-gates.sh` | ❌ W0 | ⬜ pending |
| TBD | PR A | 2 | INFRA-03 | T-1-01 | Gate script passes on a clean tree | integration | `./scripts/check-gates.sh spqr.kdf.hkdf_to_slice_spec; echo $?` → `0` | ❌ W0 | ⬜ pending |
| TBD | PR A | 2 | INFRA-03 | T-1-01 | Gate script **fails** on a deliberately broken tree — the only proof it is not a no-op | negative integration | see Negative Controls below | ❌ W0 | ⬜ pending |
| TBD | PR A | 2 | INFRA-03 | — | Its verdict matches CI's on `main` (ROADMAP criterion 2) | cross-check | run on the `origin/main` worktree; compare per gate against `gh run list --workflow lean.yml --branch main --limit 1 --json conclusion` | ❌ W0 | ⬜ pending |
| TBD | PR A | 2 | INFRA-02 | T-1-02 | Issue script dry-runs and files nothing | static + integration | `bash -n`; then run with no `--execute`; `gh issue list --state open --limit 500 --json number --jq length` unchanged before/after | ❌ W0 | ⬜ pending |
| TBD | PR A | 2 | INFRA-02 | — | Generated body matches the template shape | diff | render one body; `! grep -qE '\{[A-Z_]+\}' /tmp/body-PROP-42.md`; four gate checklist lines present | ❌ W0 | ⬜ pending |
| TBD | PR A | 2 | INFRA-02 | T-1-02 | Idempotent — no duplicate issues | integration | run `--execute` for one ID twice; second prints `SKIP … already filed as #N`; issue count unchanged | ❌ W0 | ⬜ pending |
| TBD | PR A | 2 | INFRA-02 | — | Labels created and correct | integration | `gh label list --limit 100 --json name --jq '[.[].name]'` contains all 15; re-running the label step is a no-op | ❌ W0 | ⬜ pending |
| TBD | PR A | 1 | INFRA-02 | — | D-09 rewording survives the roadmap parser | integration | `gsd-sdk query roadmap.get-phase 1` still returns the phase with 5 criteria after the edit | ✅ | ⬜ pending |
| TBD | PR A | 1 | CAT-01 | — | Template names the §12 index in its checklist | grep | `grep -q '§12' docs/ISSUE_TEMPLATE.md` | ❌ W0 | ⬜ pending |
| TBD | PR B | 3 | DEV-01..04 | — | §11 carries Decision + Status for all five rows | table parse | §11 parse check below | ❌ W0 | ⬜ pending |
| TBD | PR B | 3 | DEV-01..04 | — | PROP-42/30/43/47/50 each cite their D-row | grep | `for p in 42 30 43 47 50; do grep -A20 "^### PROP-$p " docs/spqr-properties.md \| grep -qE 'D[1-5]' \|\| exit 1; done` | ❌ W0 | ⬜ pending |
| TBD | PR B | 3 | DEV-04 | — | The caller contract is under PROP-43 in §7 | grep | `grep -A30 '^### PROP-43' docs/spqr-properties.md \| grep -q 'caller'` | ❌ W0 | ⬜ pending |
| TBD | PR B | 3 | DEV-01..04 | — | The Signal note is sendable as-is | structural | `docs/signal-deviation-questions.md` has five sections, each with spec text, code lines, impact and two candidate resolutions | ❌ W0 | ⬜ pending |

*Status: ⬜ pending · ✅ green · ❌ red · ⚠️ flaky*

### The §11 table parse check

Per the user's layout decision (Q-4, option b), §11 keeps its five-column table verbatim and
gains a **second narrow table** `| ID | Decision | Status |` directly beneath it. Assert on the
narrow table:

```bash
awk '/^## 11\./{f=1} /^## 12\./{f=0}
     f && /^\| D[1-5] \| .* \| Provisional /' docs/spqr-properties.md | wc -l
# must print 5 — one decision row per deviation, every Status cell carrying a date
```

Additionally assert the original five-column body is unchanged:

```bash
awk '/^## 11\./{f=1} /^## 12\./{f=0} f && /^\| D[1-5] \|/{n=split($0,c,"|"); print $2, n}' \
  docs/spqr-properties.md
# ten rows total: five at the wide table's field count, five at 5 (the narrow table)
```

---

## Wave 0 Requirements

- [ ] `scripts/check-gates.sh` — covers INFRA-03
- [ ] `scripts/axiom-allowlist.txt` — the gate-4 allowlist, INFRA-03
- [ ] `scripts/check-lint.sh` — rewritten as a shim for compatibility (INFRA-03)
- [ ] `scripts/create-property-issues.sh` + `scripts/property-issues.tsv` +
      `scripts/property-issue-labels.tsv` — covers INFRA-02
- [ ] `scripts/README.md` — `## Verification gates` section (INFRA-03 documentation)
- [ ] `.gitignore` — add `.gate-cache/`, `.sorry-delta-comment.md`; **remove** the `issues/`
      line (research B-1: `issues/` is gitignored and untracked, so "delete it" is only a
      reviewable diff via this line)
- [ ] `docs/signal-deviation-questions.md` — DEV-01..04 (D-11)
- [ ] A `lake build` of the working tree **and** of the `origin/main` baseline worktree
      (`lake exe cache get` first — mathlib is transitive via aeneas), before any gate task can
      be validated
- [ ] No test framework needs installing — every assertion is a shell command

---

## Negative Controls

A gate that has never failed is not known to work. Run each once in a scratch worktree or a
stashed change and paste the observed output into the phase SUMMARY.

| Gate | How to break it | Expected |
|------|-----------------|----------|
| 1 `lake build` | add a declaration in `Spqr/` that triggers a non-sorry warning | gate 1 FAIL, the warning printed |
| 2 `runLinter` | introduce a declaration the standard linter set rejects | gate 2 FAIL with an `error:` line |
| 3b sorry delta | add a one-line `sorry` theorem in a new `Spqr/Specs/` module, re-exported from `Spqr.lean` | gate 3b FAIL, the new decl listed as `direct` |
| 3b **silent-failure control** | same theorem in a module **not** re-exported from `Spqr.lean` | gate 3b **PASSES** — `Audit.lean`'s documented blind spot, and the reason the template checklist gains a re-export line. Record it. |
| 4 `#print axioms` | request a misspelled theorem name | gate 4 FAIL with `unknown identifier`, not a silent pass |
| 4 `#print axioms` | request a theorem transitively using `sorryAx` | gate 4 FAIL unless `--allow-sorry` |

Phase 1 changes no `*.lean` file, so its own sorry-delta is trivially empty — the 3b rows are
the **only** evidence that the delta path works at all. They are not optional.

---

## Manual-Only Verifications

| Behavior | Requirement | Why Manual | Test Instructions |
|----------|-------------|------------|-------------------|
| The Signal note reads as sendable prose | DEV-01..04 | Communication quality is not machine-checkable | User reads `docs/signal-deviation-questions.md` end to end and confirms each of the five questions could be sent to Signal unedited |
| Issue titles and labels are the ones the user wants filed | INFRA-02 (D-01) | D-01 requires user review of the dry-run listing before anything is filed | User reads the dry-run title+label listing and approves before any `--execute` |
| PR A / PR B base branch | — | Research Q-2: `main` contains none of the files this phase edits; `la/spec-catalog` is unmerged | Raised in PR A's stop-and-report task text, answered by the user at the PR boundary |

---

## Validation Sign-Off

- [ ] All tasks have `<automated>` verify or a Wave 0 dependency
- [ ] Sampling continuity: no 3 consecutive tasks without an automated verify
- [ ] Wave 0 covers all ❌ references above
- [ ] No watch-mode flags
- [ ] Per-task feedback latency < 5 s
- [ ] Negative-control matrix run and output recorded in SUMMARY
- [ ] `nyquist_compliant: true` set in frontmatter

**Approval:** pending
