# Phase 1: Gates, Issues and Deviation Decisions - Discussion Log

> **HISTORICAL — RE-SCOPED 2026-09-15.** This log records the discussion that produced the
> original Phase 1 (close every Open row; one GitHub issue per property). The decisions on
> issue tooling (D-01 to D-05, D-09) and the Signal note (D-11) were superseded when the goal
> became "prove as many non-trivial specs as possible". The gate decisions (D-06, D-07, D-08,
> D-08a), the deviation posture (D-10, D-12 to D-14) and the PR-boundary decisions (D-15,
> D-16, D-17) all still hold. Kept for the reasoning, not as a current contract.


> **Audit trail only.** Do not use as input to planning, research, or execution agents.
> Decisions are captured in CONTEXT.md — this log preserves the alternatives considered.

**Date:** 2026-09-14
**Phase:** 1-Gates, Issues and Deviation Decisions
**Areas discussed:** Issue set and labels, Local gate check shape, D1–D5 without Signal, PR grouping for a docs phase

---

## Issue set and labels

### Who creates the issues

| Option | Description | Selected |
|--------|-------------|----------|
| GSD runs gh issue create | Executor files from the corrected template after a dry-run review | ✓ |
| GSD drafts, user files | One markdown file per issue, user runs the batch | |
| Mixed | GSD files property issues, user files D1–D5 ones | |

### Relation to existing issues

| Option | Description | Selected |
|--------|-------------|----------|
| Fresh per-property issues, cross-link | New issues link #44 and #510–#533 as related; nothing edited | ✓ |
| Fresh issues, and close #44 | Same plus a closing comment on #44 | |
| Reuse where one exists | Adopt per-function issues where they cover the property | |

### Label scheme

| Option | Description | Selected |
|--------|-------------|----------|
| Template scheme, create labels | `type:*`, `status:open/axiom/proved-branch/proved`, created idempotently | ✓ |
| Existing repo labels only | `Proof` / `Specification` / `Infrastructure` | |
| Both | Template labels plus `Proof` | |

### Non-property requirements

| Option | Description | Selected |
|--------|-------------|----------|
| Issues for everything with a PR | INFRA, MERGE-04..07, AXIOM, DEV, CAT all get issues | ✓ |
| Properties only | Ad-hoc issues at PR time for the rest | |

### Old `issues/` tooling

| Option | Description | Selected |
|--------|-------------|----------|
| Replace with new script | New idempotent script; stale preview deleted in the same PR | ✓ |
| Leave untouched, new script elsewhere | Two schemes remain in tree | |
| Generate bodies only, no script | No reusable script kept | |

**Notes:** none beyond the selections.

---

## Local gate check shape

### Location

| Option | Description | Selected |
|--------|-------------|----------|
| Extend scripts/check-lint.sh | Already CI-identical for gates 1 and 2; add sections | ✓ |
| New scripts/check-gates.sh calling check-lint.sh | Layered separation | |
| Documented command sequence only | No script | |

### Sorry-manifest baseline

| Option | Description | Selected |
|--------|-------------|----------|
| Build main in a git worktree | Exact CI parity; first run costs a full build | ✓ |
| Commit a baseline manifest | Drifts unless CI enforces it | |
| Fail on any Spqr.Specs sorry | Skip the delta | |

### `#print axioms` targets

| Option | Description | Selected |
|--------|-------------|----------|
| Theorem names as arguments | Scratch Lean file, grep against allowlist | ✓ |
| Extend Audit.lean with allowlist check | Whole-project coverage, touches CI script | |
| Both | | |

### CI parity

| Option | Description | Selected |
|--------|-------------|----------|
| Local only, CI unchanged | lean.yml keeps inline steps | ✓ |
| CI calls the script | Refactor a required check | |

**Notes:** rename to `check-gates.sh` left to the planner.

---

## D1–D5 without Signal

### What counts as a recorded decision

| Option | Description | Selected |
|--------|-------------|----------|
| Provisional: code is authoritative | Status Provisional, question quoted, phase does not wait | ✓ |
| Block on Signal | Phase stays open until Signal rules | |
| Provisional, but D1 is different | D1 escalated before PROP-42 is touched | |

### Contacting Signal

| Option | Description | Selected |
|--------|-------------|----------|
| GSD drafts one note, user sends it | `docs/signal-deviation-questions.md` | ✓ |
| Questions live only in §11 | | |
| User handles it entirely | | |

### §11 format

| Option | Description | Selected |
|--------|-------------|----------|
| Add Decision and Status columns | Single table kept | ✓ |
| One subsection per deviation | | |
| Table plus a decisions log below | | |

### D5 caller contract location

| Option | Description | Selected |
|--------|-------------|----------|
| Catalog §7 under PROP-43 | §11 D5 points to it | ✓ |
| Separate docs/caller-contract.md | | |
| Both | | |

---

## PR grouping for a docs phase

### Number of PRs

| Option | Description | Selected |
|--------|-------------|----------|
| Three PRs (infra, deviations, none for issues) | Effectively two PR boundaries | ✓ |
| One PR per requirement | Eight draft PRs | |
| Two PRs: infra, deviations | Issue filing inside infra execution | |
| One PR for the whole phase | | |

### Order

| Option | Description | Selected |
|--------|-------------|----------|
| Infra first, then issues, then D1–D5 | Every PR closes an existing issue | ✓ |
| D1–D5 first | | |

### Issue timing

| Option | Description | Selected |
|--------|-------------|----------|
| After the infra PR merges | Batch from the merged template | |
| During execution, from the branch | Batch from the branch | |
| Free text | "create issues one by one, when we're done with a PR we create the issue it can close" | ✓ |

**User's choice:** just-in-time issue filing at each PR boundary.
**Notes:** Claude flagged that this changes INFRA-02 and Phase 1 success criterion 3, and offered (1) just-in-time with INFRA-02 reworded, or (2) batch for Phases 1–2 only. User chose option 1.

### `check_no_sorry` mentions outside the template

| Option | Description | Selected |
|--------|-------------|----------|
| Reword to 'no nonexistent gates' | Warning kept, token removed | ✓ |
| Only fix the template | | |
| Remove all mentions | | |

---

## Claude's Discretion

- Rename of `check-lint.sh` to `check-gates.sh`.
- Exact template checklist wording.
- Issue script implementation style.
- Where the gate script is documented.

## Deferred Ideas

- CI calling the gate script.
- Audit.lean allowlist check with non-zero exit.
- Closing or retitling #44 and #510–#533.
