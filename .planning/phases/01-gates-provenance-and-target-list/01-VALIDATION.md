---
phase: 1
slug: gates-provenance-and-target-list
status: draft
flag_owner: plan 01-04 task 3 flips nyquist_compliant and wave_0_complete to true, and only when all nine negative controls are recorded with literal output
nyquist_compliant: false
wave_0_complete: false
created: 2026-09-14
rescoped: 2026-09-15
---

# Phase 1 — Validation Strategy

> Per-phase validation contract for feedback sampling during execution.
> Derived from `01-RESEARCH.md` § Validation Architecture.
>
> **Re-scoped 2026-09-15.** The goal became *prove as many non-trivial specs as possible*,
> with provenance (PROV-01) and a binding statement review (REV-01); issue automation was
> dropped. Plan numbers below refer to the **new** plan set. The superseded plans are in
> `.planning/archive/01-superseded-2026-09-15/`. Two substantive changes here: a fifth gate
> (provenance) with its own controls, and INFRA-02's rows removed.

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
| **Quick run command** | `bash -n scripts/check-gates.sh && python3 -c "import ast; ast.parse(open('scripts/check-provenance.py').read())" && git grep -n '<phantom>' -- ':!.planning'` (expect exit 1 / no output) |
| **Full suite command** | `./scripts/check-gates.sh <explicit #print axioms targets>` — all **five** gates, with the baseline present. `scripts/create-property-issues.sh` is **not** a deliverable of this phase (issue automation was dropped 2026-09-15) and must not appear in any validation path |
| **Estimated runtime** | quick ~2 s; full suite dominated by `lake build` — minutes warm, **first run costs a cold `lake exe cache get` + full build of the `origin/main` worktree** (research B-5) |

---

## Sampling Rate

- **After every task commit:** `bash -n` on any touched script + the scoped `<phantom>` grep +
  the **structural** catalog check if `docs/spqr-properties.md` changed — the existing
  five-column §11 table still parses with its five D-rows, and the registry/`Source:` structure
  is intact. Seconds.
- **The §11 *decision-table* assertions below (five `Provisional` rows, ten deviation rows in
  total) apply only from plan 01-08 task 1 onward**, because 01-08 in wave 7 is what creates the
  second table. Running them earlier reports `Provisional decision rows: 0` against a catalog
  that is correct for its stage: 01-03 (wave 2) adds a `Source` column and 01-07 (wave 6) adds
  two rows, and neither is supposed to create a decision row. Before 01-08, a zero count is the
  expected reading, not a failure.
- **Waves 1-2, before the tree is built:** static checks only — `bash -n`,
  `python3 -c "import ast; ast.parse(...)"`, the scoped `<phantom>` grep, and gate 5 run alone
  (`--gates 5`, which needs no `lake`). A full gate run is **impossible** here and its absence
  is not evidence of a defect: plan 01-02 writes the runner without running it, 01-03 supplies
  gate 5's reference lists in wave 2, and the built tree and baseline arrive only with 01-04 in
  wave 3. Gate 5's *expected-red* run before 01-03 fills the citations is a required observation,
  not a failure.
- **From wave 3 on, and at each PR boundary (A and B):** the **full** gate run
  `./scripts/check-gates.sh <targets>` — with explicit `#print axioms` targets and with the
  baseline present, so gates 3b and 4 actually execute. A bare `./scripts/check-gates.sh`
  with no targets skips gate 4 by design and is a *partial* run: it may not be cited as the
  boundary check. The script distinguishes the two in its summary line
  (`ALL GATES PASSED` vs `PASSED WITH SKIPS: …`); only the former discharges a boundary.
  Plus the complete requirement→validation table below. There is **no** issue-script step:
  `scripts/create-property-issues.sh` is not a deliverable of this phase.
- **Before `/gsd:verify-work`:** the negative-control matrix has been run once and its observed
  output pasted into the phase SUMMARY.
- **Max feedback latency:** 5 s for per-task checks; gate-script runs are build-bound and are
  deliberately not per-task.

---

## Per-Task Verification Map

Task IDs are assigned by the planner and refer to `<plan> T<n>` in
`.planning/phases/01-gates-issues-and-deviation-decisions/01-NN-PLAN.md`. Each row below is a
requirement-level obligation that the named task carries as an `<automated>` verify or an
`<acceptance_criteria>` assertion. Wave numbers match the plan frontmatter.

| Task ID | Plan | Wave | Requirement | Threat Ref | Secure Behavior | Test Type | Automated Command | File Exists | Status |
|---------|------|------|-------------|------------|-----------------|-----------|-------------------|-------------|--------|
| 01-01 T1 | PR A | 1 | INFRA-01 | — | Template names four gates by command + a catalog-and-index line | grep assertion | `grep -c '^- \[ \] `lake' docs/ISSUE_TEMPLATE.md` ≥ 3; `grep -q 'print axioms' docs/ISSUE_TEMPLATE.md`; `grep -q '§12' docs/ISSUE_TEMPLATE.md` | ❌ W0 | ⬜ pending |
| 01-01 T2 | PR A | 1 | INFRA-01 | — | No operative document cites a gate that does not exist | grep assertion | `git grep -n '<phantom>' -- ':!.planning'` exits 1 with no output | ❌ W0 | ⬜ pending |
| 01-02 T1 | PR A | 1 | INFRA-03 | — | Gate script is syntactically valid | static | `bash -n scripts/check-gates.sh` | ❌ W0 | ⬜ pending |
| 01-04 T1 | PR A | 3 | INFRA-03 | T-1-01 | Gate script passes on a clean tree | integration | `./scripts/check-gates.sh spqr.kdf.hkdf_to_slice_spec; echo $?` → `0` | ❌ W0 | ⬜ pending |
| 01-04 T3 | PR A | 3 | INFRA-03 | T-1-01 | Gate script **fails** on a deliberately broken tree — the only proof it is not a no-op | negative integration | see Negative Controls below | ❌ W0 | ⬜ pending |
| 01-04 T2 | PR A | 3 | INFRA-03 | — | Its verdict matches CI's on `main` (ROADMAP criterion 2) | cross-check | invoke the **working tree's** script by absolute path with the `origin/main` worktree as CWD (`origin/main` has no `check-gates.sh`); compare per gate against the `lean.yml` run whose `headSha` equals `git rev-parse origin/main`. Gates 1–2 are directly comparable; gate 3b is local-only policy (CI reports, does not fail); gate 4 has no CI step | ❌ W0 | ⬜ pending |
| 01-01 T1 | PR A | 1 | CAT-01 | — | Template names the §12 index in its checklist | grep | `grep -q '§12' docs/ISSUE_TEMPLATE.md` | ❌ W0 | ⬜ pending |
| 01-08 T1 | PR B | 7 | DEV-01..04 | — | §11 carries Decision + Status for all five rows | table parse | §11 parse check below | ❌ W0 | ⬜ pending |
| 01-08 T2 | PR B | 7 | DEV-01..04 | — | PROP-42/30/43/47/50 each cite their D-row | grep | `for p in 42 30 43 47 50; do grep -A20 "^### PROP-$p " docs/spqr-properties.md \| grep -qE 'D[1-5]' \|\| exit 1; done` | ❌ W0 | ⬜ pending |
| 01-08 T2 | PR B | 7 | DEV-04 | — | The caller contract is under PROP-43 in §7 | grep | `grep -A30 '^### PROP-43' docs/spqr-properties.md \| grep -q 'caller'` | ❌ W0 | ⬜ pending |

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

| 01-03 T2 | PR A | 2 | PROV-01 | T-1-06 | Every catalog row has a resolving `Source:` | integration | `python3 scripts/check-provenance.py` exits 0, or fails only on user-ruled `Unsourced` rows | ❌ W0 | ⬜ pending |
| 01-03 T2 | PR A | 2 | PROV-01 | T-1-08 | The checker sees the whole catalog, not half | integration | ID-set agreement with the §12 index — 42 registry entries against 38 index rows, empty symmetric difference once D1–D5 maps to its aggregate; below 37 non-deviation entries it fails by construction. The two counts are **not** equal | ❌ W0 | ⬜ pending |
| 01-06 T1 | PR B | 5 | CAT-03 | T-1-13 | Every obligation has a band and three verdicts, no `TBD` | structural | one row per registry entry (42 at 01-06, before 01-07 adds two); per-band counts reconcile with `REQUIREMENTS.md`'s work-unit figure of 22 or the discrepancy is reported | ❌ W0 | ⬜ pending |
| 01-06 T3 | PR B | 5 | REV-01 | T-1-18 | The review runs read-only and cannot write the repo | integration | the skill invokes `codex exec --sandbox read-only`; a sandbox startup failure is a STOP, not a fallback | ❌ W0 | ⬜ pending |
| 01-07 T3 | PR B | 6 | REV-01 | T-1-21 | The machinery ran for real on two statements | integration | ≥1 persisted artifact per statement under `docs/statement-reviews/` with model+effort in its header; a log row per round | ❌ W0 | ⬜ pending |
| 01-07 T3 | PR B | 6 | REV-01 | T-1-11 | An ACCEPT cannot travel to an edited statement | structural | every log row carries a `sha256` of the reviewed text; each REVISE round records both SHAs | ❌ W0 | ⬜ pending |
| 01-07 T3 | PR B | 6 | REV-01 | T-1-22 | No proof predates its ACCEPT | structural | `git status --porcelain -- '*.lean'` empty in 01-07 (tasks 2 and 3 both); log dates make the ordering checkable | ❌ W0 | ⬜ pending |

---

## Wave 0 Requirements

- [ ] `scripts/check-gates.sh` — covers INFRA-03
- [ ] `scripts/axiom-allowlist.txt` — the gate-4 allowlist, INFRA-03
- [ ] `scripts/check-lint.sh` — rewritten as a shim for compatibility (INFRA-03)
- [ ] `scripts/check-provenance.py` — the gate-5 provenance checker (PROV-01)
- [ ] `docs/spec-sections.txt` + `docs/scka-refs.txt` — the two transcribed reference lists
      gate 5 resolves spec and SCKA citations against (PROV-01)
- [ ] `docs/spqr-properties.md` `Source:` retrofit — without it gate 5 is red for a reason
      unrelated to the script (PROV-01)
- [ ] `docs/proof-targets.md` — the per-row band and C1/C2/C3 record (CAT-03)
- [ ] `docs/rubrics/spqr-statement-review.md` + `.claude/skills/spqr-statement-review/SKILL.md`
      + `docs/spec-review-log.md` — the REV-01 machinery
- [ ] `codex` reachable with `~/.secrets/openrouter` sourced — REV-01's reviewer is
      cross-engine, so a Codex preflight failure blocks plans 01-06 and 01-07
- [ ] `scripts/README.md` — `## Verification gates` section (INFRA-03 documentation)
- [ ] `.gitignore` — add `.gate-cache/` and `.sorry-delta-comment.md`. The `issues/` line
      stays: no issue tooling is built, so there is nothing to retire
- [ ] A `lake build` of the working tree **and** of the `origin/main` baseline worktree
      (`lake exe cache get` first — mathlib is transitive via aeneas), before the
      **build-dependent** gates can be validated: gates 1, 2, 3a, 3b and 4. Gate 5 and every
      static check need no build and are validated in waves 1–2 without one; plan 01-04 in
      wave 3 is what supplies the build, so its absence before then is the schedule working,
      not a gap
- [ ] No test framework needs installing — every assertion is a shell command

---

## Negative Controls

A gate that has never failed is not known to work. Run each once in a **throwaway
`git worktree`** and paste the observed output into the phase SUMMARY. Never park a breakage in
`git stash`: this checkout carries five pre-existing stashes that are the user's work, the
negative-control contract is "no *new* stash" against a recorded `STASH_BASELINE`, and no
pre-existing stash may be dropped, popped or cleared (01-04 task 3).

| Gate | How to break it | Expected |
|------|-----------------|----------|
| 1 `lake build` | add a declaration in `Spqr/` that triggers a non-sorry warning | gate 1 FAIL, the warning printed |
| 2 `runLinter` | introduce a declaration the standard linter set rejects | gate 2 FAIL with an `error:` line |
| 3b sorry delta | add a one-line `sorry` theorem in a new `Spqr/Specs/` module, re-exported from `Spqr.lean` | gate 3b FAIL, the new decl listed as `direct` |
| 3b **silent-failure control** | same theorem in a module **not** re-exported from `Spqr.lean` | gate 3b **PASSES** — `Audit.lean`'s documented blind spot, and the reason the template checklist gains a re-export line. Record it. |
| 4 `#print axioms` | request a misspelled theorem name | gate 4 FAIL with `unknown identifier`, not a silent pass |
| 4 `#print axioms` | request a theorem transitively using `sorryAx` | gate 4 FAIL unless `--allow-sorry` |
| 3a `Audit.lean` | break an import `Audit.lean` needs so the run exits non-zero | gate 3a FAIL, **not** SKIP — a gate that could not run is never a pass |
| 4 **wrapped-list control** | force a wrapped axiom list with `set_option format.width 20` in the scratch file (`format.width` is a registered builtin option, `Lean/Data/Format.lean:23`), confirm from the raw log that the list spans more than one line, then drop one **continuation-line** axiom from the allowlist | gate 4 FAIL naming it. A pass means the matcher is line-oriented and silently ignores wrapped axioms — a false green. Lean joins the list with `"," ++ Format.line` (`Lean/Message.lean:414-417`), a soft break that becomes a newline past the print width. **If no route produces a wrapped report, STOP** — an unwrapped log is not evidence about a wrapped list, so the control stays unmet and the flags stay `false`. |
| 5 provenance | corrupt one `Source:` citation four ways, one at a time: nonexistent file; line range past end of file; a `Spec §x.y` absent from `docs/spec-sections.txt`; an unparseable form | gate 5 FAIL naming the row, each time. An unrecognised citation form must fail, not skip — otherwise a typo buys a pass |

Phase 1 changes no `*.lean` file, so its own sorry-delta is trivially empty — the 3b rows are
the **only** evidence that the delta path works at all. They are not optional.

All nine rows are mandatory, and none may be satisfied by a pass: for every row except the
3b silent-failure control, a **pass is the failure condition**. The gate-5 row counts as one
control with four recorded corruptions, all four required.

---

## Manual-Only Verifications

| Behavior | Requirement | Why Manual | Test Instructions |
|----------|-------------|------------|-------------------|
| A row that cannot be grounded is `Unsourced`, not plausibly cited | PROV-01 | "no source exists for this" is a claim about the source documents, not about the tree | Plan 01-03 task 3: user rules on every `Unsourced` row and on a sample of spec-cited rows |
| The band assignments are the ones intended | CAT-03 | The bands are the basis of the goal; a misbanded row silently changes scope | Plan 01-06 task 4: user approves flagged band changes, the target count, and any orphan support lemma |
| The vacuity threshold in the review rubric | REV-01 | The check most likely to reject real work and to catch a worthless proof; the threshold is a judgement call | Plan 01-06 task 4: user reads the vacuity section and owns the threshold |
| STRUCT-02a's and STRUCT-02b's shape, PROP-35's **derived** `Domain:` line, PROP-37's `Finding:` annotation with its Phase 7 deferral, and any REJECT or HUMAN_RULING | REV-01 | A witness theorem can look vacuous and a hand-written canonicity predicate can look chosen to fit; PROP-35's domain was found incomplete twice when hand-listed; PROP-37's restatement was deferred because representability alone is insufficient | Plan 01-07 task 4: user rules; re-wording a REJECT into an ACCEPT after asking is forbidden; a first-statement REJECT resumes at the second statement rather than ending task 3 |
| The reviewer saw only the cited source | REV-01 | A leak is visible only by reading the assignment extract | Plan 01-07 task 3: user checks the pasted extract for neighbouring catalog rows |
| PR A / PR B base branch, and the PR B branch | — | Research Q-2: `main` contains none of the files this phase edits; `la/spec-catalog` is unmerged and `branching_strategy` is `none` | Plan 01-05 raises both; a bare "skip" does not waive the PR B branch answer, and plan 01-06 stops without it |

---

## Validation Sign-Off

- [ ] All tasks have `<automated>` verify or a Wave 0 dependency
- [ ] Sampling continuity: no 3 consecutive tasks without an automated verify
- [ ] Wave 0 covers all ❌ references above
- [ ] No watch-mode flags
- [ ] Per-task feedback latency < 5 s
- [ ] Negative-control matrix run and output recorded in SUMMARY — **all nine rows**, the
      wrapped-axiom-list control included; it cannot be waived
- [ ] `nyquist_compliant: true` set in frontmatter

**Approval:** pending
