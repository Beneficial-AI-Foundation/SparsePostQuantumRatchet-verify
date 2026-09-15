---
phase: 01-gates-provenance-and-target-list
plan: 01
subsystem: infra
tags: [docs, gates, provenance, statement-review, pr-checklist, rubric]

# Dependency graph
requires: []
provides:
  - "docs/ISSUE_TEMPLATE.md is a per-property PR checklist: REV-01/PROV-01 preconditions, the five real gates, the Spqr.lean re-export trap, the CAT-01 catalog-and-§12 line, and the scripts/check-gates.sh one-command runner"
  - "No tracked file outside .planning/ cites a gate that does not exist in this repository"
  - "Plan-review rubric checks provenance, statement review and C3 band scope, and names the fifth gate"
  - "CLAUDE.md Gates bullet names five gates and the check-gates.sh runner"
affects: [01-02 gate scripts, 01-03 statement-review skill and log, 01-04 proof-targets, every later property PR]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "Forward references by final path: the checklist names scripts/check-gates.sh, scripts/check-provenance.py, scripts/axiom-allowlist.txt, docs/spec-review-log.md and docs/proof-targets.md before plans 01-02/01-03/01-04 create them"
    - "Preconditions vs gates split: REV-01 and PROV-01 are conditions for starting proof work, not boxes ticked at PR time"

key-files:
  created: []
  modified:
    - docs/ISSUE_TEMPLATE.md
    - docs/rubrics/spqr-plan-review.md
    - CLAUDE.md

key-decisions:
  - "The Source field in the template was restated under the PROV-01 three-class grammar instead of being left with the old tag vocabulary (production-code, spec-mlkembraid, hax-kat, ...), which no gate can check"
  - "Added Band and Evidence fields to the template: Band carries the C3 verdict from docs/proof-targets.md, Evidence carries non-PROV-01 pointers outside the gate's grammar"
  - "The band scope error became a new rubric item 10 rather than an edit to item 9, so existing item numbers (item 7 is cited by plans and reviews) keep their meaning"
  - "REQUIREMENTS.md was left untouched to avoid a merge conflict with the other wave-1 worktrees; the orchestrator marks INFRA-01"

patterns-established:
  - "Checklist gate lines are copy-runnable commands, each with the condition that makes it pass"
  - "A support lemma needs its own `scope: support` ACCEPT; it is never counted as a target"

requirements-completed: [INFRA-01, CAT-01]

# Metrics
duration: 7min
completed: 2026-09-15
---

# Phase 01 Plan 01: Honest Operative Documents Summary

**docs/ISSUE_TEMPLATE.md is now a per-property PR checklist naming the five real gates, the REV-01/PROV-01 preconditions and the §12 catalog obligation; the phantom gate token is gone from every tracked file outside .planning/.**

## Performance

- **Duration:** 7 min
- **Started:** 2026-09-15T13:09:58Z
- **Completed:** 2026-09-15T13:17:26Z
- **Tasks:** 2
- **Files modified:** 3

## Accomplishments

- `docs/ISSUE_TEMPLATE.md` rewritten as `# SPQR Property — PR Checklist`: the Labels section and the issue vocabulary are gone, `## Property: {PROP-ID}` is preserved byte for byte, and the checklist is split into preconditions (target recorded in `docs/proof-targets.md`, resolving `Source:`, an ACCEPT in `docs/spec-review-log.md` dated before the first proof commit, a separate `scope: support` ACCEPT for support lemmas) and gates (`lake build`, `lake exe runLinter Spqr`, `lake env lean scripts/Audit.lean`, `#print axioms`, `python3 scripts/check-provenance.py`, plus the `Spqr.lean` re-export and the CAT-01 status/section/§12 line, with `./scripts/check-gates.sh <theorem-names>` as the one command).
- Rubric item 7 now names five gates, the `check-gates.sh` runner, and fails a plan that claims a property proved without a resolving citation or schedules proof work with no prior ACCEPT.
- New rubric item 10 makes an evaluation-band or single-path-band goal a scope error rather than an approvable target.
- `CLAUDE.md`'s Gates bullet names five gates, the runner, and no nonexistent gate; all seven `GSD:` marker pairs intact (14 marker lines).
- The repo-wide phantom-token grep over tracked files outside `.planning/` exits 1 with no output — ROADMAP criterion 6.

## Task Commits

1. **Task 1: Rewrite docs/ISSUE_TEMPLATE.md as a per-property PR checklist** - `be8bf78` (docs)
2. **Task 2: Remove the phantom token from the rubric and CLAUDE.md, add the provenance/statement-review/band checks** - `97e0d25` (docs)

## Files Created/Modified

- `docs/ISSUE_TEMPLATE.md` - per-property PR checklist (153 lines): property identity and typing fields, Band, PROV-01 `Source:` grammar, `Evidence:`, Description, Formal Definition, Lean Provability, preconditions block, gates block, user-opens-the-draft-PR closing note
- `docs/rubrics/spqr-plan-review.md` - item 7 rewritten (five gates, provenance and statement-review failure conditions); item 10 added (band scope error); authority hierarchy item 3 extended with `docs/proof-targets.md` and `docs/spec-review-log.md`
- `CLAUDE.md` - Gates bullet reworded inside the `GSD:project` block; no structural change to any marked block

## Decisions Made

- The template's `**Source:**` tag list (`production-code`, `spec-mlkembraid`, `hax-kat`, ...) was replaced by the PROV-01 three-class grammar. Leaving it would have told contributors to write citations `scripts/check-provenance.py` cannot parse, reintroducing the exact defect this plan removes in a different place.
- `Band:` and `Evidence:` fields were added. `Band` is the C3 verdict the preconditions block requires from `docs/proof-targets.md`; `Evidence` is where non-PROV-01 pointers go, which is what keeps the `Source:` line inside the gate's grammar.
- The band scope error landed as a new item 10 instead of an edit to item 9. Item numbers in this rubric are cited by plans and by review artifacts, so renumbering or repurposing an item would silently invalidate those citations.
- `.planning/REQUIREMENTS.md` was not edited. Wave 1 runs several worktree agents against the same file; the orchestrator marks INFRA-01 centrally after merge. INFRA-01 is fully satisfied by this plan. CAT-01 is satisfied only *structurally* here (the obligation is on the checklist); it stays open as a per-PR obligation for every later phase.

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 2 - Missing Critical] Restated the template's `Source:` field under the PROV-01 grammar**
- **Found during:** Task 1
- **Issue:** The plan's keep-list did not mention the `**Source:**` block, which carried the pre-PROV-01 tag vocabulary. A checklist instructing a contributor to write `spec-mlkembraid` or `hax-kat` produces citations the provenance gate cannot resolve — the same class of defect as citing a nonexistent gate.
- **Fix:** Rewrote the `Source:` comment to the three PROV-01 classes with the semicolon rule and the "every listed citation must resolve" condition; added an `Evidence:` field for pointers outside the grammar.
- **Files modified:** docs/ISSUE_TEMPLATE.md
- **Verification:** `grep -q 'check-provenance'` and the full Task 1 automated check pass; no phantom token.
- **Committed in:** `be8bf78`

**2. [Rule 2 - Missing Critical] Extended the rubric's authority hierarchy with the two new records**
- **Found during:** Task 2
- **Issue:** Item 7's new checks direct a reviewer to `docs/spec-review-log.md` and (via band) `docs/proof-targets.md`, but the authority hierarchy listed neither, so a reviewer had no standing to treat them as accepted records.
- **Fix:** Added both to authority item 3 with a one-clause description of what each carries.
- **Files modified:** docs/rubrics/spqr-plan-review.md
- **Verification:** `grep -q 'spec-review-log'` passes; the working-tree status for this task listed only the two planned files.
- **Committed in:** `97e0d25`

---

**Total deviations:** 2 auto-fixed (both Rule 2, missing critical)
**Impact on plan:** Both keep the edited documents internally consistent with the gate that plan 01-02 builds. No scope creep: zero new files, three files touched, zero Lean and zero `src/` hunks.

## Issues Encountered

- The worktree was created from `main` (`e8f6689`) instead of the expected base `a8b7a32` on `la/spec-catalog`. A hard reset was unavailable, so the per-agent branch was repointed with `checkout -B worktree-agent-<id> a8b7a32` — a per-agent ref only, no protected ref touched. HEAD was verified at `a8b7a32` with a clean tree before any edit.
- Forward-referenced paths (`scripts/check-gates.sh`, `scripts/check-provenance.py`, `scripts/axiom-allowlist.txt`, `docs/spec-review-log.md`, `docs/proof-targets.md`, the `/spqr-statement-review` skill) do not exist yet. The plan directs referencing them by final path; plans 01-02 through 01-04 create them. Nothing in this plan executes them.

## Verification

| Check | Result |
|---|---|
| Phantom-token grep over tracked files outside `.planning/` | exit 1, no output |
| Task 1 automated check (token absent, `check-gates.sh`, `spec-review-log`, `check-provenance`, `§12`, identity line, no Labels) | pass |
| `grep -c 'lake ' docs/ISSUE_TEMPLATE.md` | 3 (at least 3 required) |
| `grep -ci 'issue' docs/ISSUE_TEMPLATE.md` | 1 — the line stating there are none |
| Rubric strings (`a gate that does not exist in this repository`, `check-provenance`, `spec-review-log`, `evaluation-band`/`single-path`) | all present |
| Seven `GSD:` marker pairs by name; 14 marker lines | pass |
| Status over `src`, `SrcTranslated`, `*.lean` | empty |
| `lake` invocations | none, as required by the plan's `phase_type` |

## User Setup Required

None - no external service configuration required.

## Next Phase Readiness

- Plan 01-02 can build `scripts/check-gates.sh` and `scripts/check-provenance.py` against the exact invocations the checklist and the rubric now promise: `./scripts/check-gates.sh <theorem-names>` and `python3 scripts/check-provenance.py`.
- Plan 01-03 must create `docs/spec-review-log.md` and the `--support` flag of `/spqr-statement-review`; both are named as preconditions in the checklist.
- Plan 01-04 must record a `Band` per obligation in `docs/proof-targets.md`; the template's `Band:` field and rubric item 10 both read from it.
- No blockers.

---
*Phase: 01-gates-provenance-and-target-list*
*Completed: 2026-09-15*
