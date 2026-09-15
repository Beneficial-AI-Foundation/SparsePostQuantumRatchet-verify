# Phase 1: Gates, Provenance and the Reviewed Target List - Context

> **RE-SCOPED 2026-09-15.** The phase goal changed from "close every Open catalog row, one
> GitHub issue per property" to "prove as many non-trivial specs as possible", with
> provenance (PROV-01) and a binding statement review (REV-01). Issue automation is out of
> scope.
>
> **Still live in this document** — the new plan set cites these by line range:
> - the gate-4 `#print axioms` recipe, the 20-name allowlist table and the three naming traps
> - the assumptions log, in particular A1 (output shapes, unknown-name behaviour) and A2
>   (`opaque` invisibility), both still requiring the plan 01-04 probe
> - the pitfalls: P-1 (the gate that passes on a misspelled name), P-5, P-7, P-8
> - the environment facts: `shellcheck` absent, the tree unbuilt, mathlib transitive via aeneas
> - blocker B-4 and question Q-2 on the PR base branch
>
> **Superseded** — ignore these sections:
> - everything on `scripts/create-property-issues.sh`, the TSV data files, the label scheme
>   and the `gh issue` invocations (D-01 to D-05, D-09)
> - the retirement of the legacy `issues/` tooling (D-05); `issues/` stays untracked
> - the Signal deviation note (D-11); deferred to v2 as DEV-05
> - the plan numbering; see `.planning/archive/01-superseded-2026-09-15/README.md` for the map
>
> New material the re-scope added is **not** in this document: the band taxonomy, the
> provenance gate design and the statement-review machinery are specified in
> `.planning/PROJECT.md`, `.planning/REQUIREMENTS.md` and plans 01-02, 01-03, 01-06 and 01-07.


**Gathered:** 2026-09-14
**Status:** Ready for planning

<domain>
## Phase Boundary

A docs-and-process phase. It corrects the per-property issue template so it
names the four real gates, adds a repeatable local gate check that reproduces
CI, replaces the stale issue tooling under `issues/` with a script that files
one issue per property from the corrected template, and records a decision
for each of D1–D5 in `docs/spqr-properties.md` §11 so that the theorem
statements of Phases 5–6 are written once. No Lean proofs, no `src/` change,
no CI workflow change.

Requirements: INFRA-01, INFRA-02 (reworded, see D-09), INFRA-03, CAT-01,
DEV-01, DEV-02, DEV-03, DEV-04.

</domain>

<decisions>
## Implementation Decisions

### Issue set and labels
- **D-01:** GSD files issues itself with `gh issue create`. Issues are not
  PRs, so the "user opens every PR" rule is untouched. The user reviews a
  dry-run listing (title + labels) before anything is filed.
- **D-02:** Fresh per-property issues. Each body cross-links overlapping
  per-function issues (#510–#533) and the umbrella #44 as "related". GSD
  does not close, retitle or relabel any existing issue.
- **D-03:** Label scheme is the template's: `type:*` and
  `status:open | status:axiom | status:proved-branch | status:proved`, created
  once by an idempotent step. Catalog status and issue label stay one-to-one.
  Repo labels `Proof`, `Specification`, `Infrastructure`, `Sorry` are not
  used for these issues.
- **D-04:** Every deliverable that lands via a PR gets an issue: property rows
  and also INFRA, MERGE-04..07, AXIOM, DEV and CAT requirements. Non-property
  issues use `type:proof-infra` or `spec-deviation`.
- **D-05:** A new idempotent script (labels + issue bodies from the template,
  dry-run by default, `--execute` to file) replaces `issues/create_issues.sh`.
  `issues/SPQR_ISSUES_PREVIEW.md` and `issues/272/` are deleted in the same
  PR. One source of truth for issue bodies.

### Local gate check
- **D-06:** Extend `scripts/check-lint.sh`, which already runs gates 1 and 2
  byte-for-byte as `.github/workflows/lean.yml`, with three further sections:
  `lake env lean scripts/Audit.lean`, a sorry-manifest delta, and
  `#print axioms`. Renaming to `check-gates.sh` with a compatibility note is
  the planner's call.
- **D-07:** Baseline for the sorry-manifest delta: the script creates or
  updates a git worktree at `origin/main`, runs `Audit.lean` there once and
  caches the resulting manifest under a gitignored path. This reproduces
  CI's cached-main-manifest comparison exactly. First run costs a full
  build of `main`.
- **D-08:** `#print axioms` targets are theorem names passed as script
  arguments. The script writes a scratch Lean file with one `#print axioms`
  per name and greps the output against the allowlist: `propext`,
  `Classical.choice`, `Quot.sound` and the documented stubs of catalog §1.
  No change to `Audit.lean`.
- **D-08a:** Local only. `lean.yml` is not modified. Success criterion 2 is
  met by running the script on `main` and comparing with CI's result.

### Issue timing and INFRA-02 rewording
- **D-09:** Issues are filed just-in-time, not in a batch. When a PR's work
  is complete and verified, GSD runs the issue script for that single
  deliverable, then stops at the PR boundary and reports the issue number so
  the user opens the PR with `Closes #N`. Consequences, to be applied by the
  planner in the same phase:
  - INFRA-02 is reworded to: "A repeatable script files one issue per
    property from the corrected template; each PR's issue is created at its
    PR boundary, before the user opens the PR."
  - Success criterion 3 of Phase 1 drops the "one open issue per v1
    property" count; it becomes "the issue script files a correctly
    labelled issue from the template, demonstrated on the Phase 1 issues".
  - The roadmap references property IDs, not issue numbers, in later phases.
  - REQUIREMENTS.md and ROADMAP.md changes go through `gsd-sdk` handlers,
    not direct edits.

### D1–D5 without a Signal ruling
- **D-10:** A "recorded decision" while Signal is silent is
  `Status = Provisional`, `Decision = code as implemented is authoritative`.
  Properties are stated against the code now. Phase 1 does not wait on
  Signal. A later ruling flips Status to Decided with a date and, if it
  disagrees with the code, opens a restatement issue for the affected
  property.
- **D-11:** GSD drafts `docs/signal-deviation-questions.md`: five questions,
  each with the spec text, the code lines, the impact and the two candidate
  resolutions, ready to send. The user sends it through their own channel.
  Answers are pasted back into §11.
- **D-12:** §11 keeps its single table and gains two columns: `Decision` and
  `Status` (Provisional / Decided, with date). No per-deviation subsections.
- **D-13:** D5's caller contract (MAC failure returns `Err`, the caller keeps
  the previous state and may retry, the library does not abort the session)
  is written out in catalog §7 under PROP-43. §11 row D5 points to it. The
  AUTH-01 theorem in Phase 5 quotes it.
- **D-14:** The catalog text for PROP-30, PROP-47, PROP-50 and PROP-43 is
  reviewed so each states the provisional behaviour explicitly and cites the
  D-row (D2, D3/D4, D5) so Phases 5–6 can quote it verbatim. PROP-42 §5 is
  aligned with the D1 provisional decision.

### PR grouping and order
- **D-15:** Two PR boundaries, not eight:
  - PR A (infra): template fix, CAT-01 checklist line, extended gate script,
    issue script and label creation, removal of `issues/`, `check_no_sorry`
    rewording. Closes the INFRA-01/02/03 and CAT-01 issues.
  - PR B (deviations): §11 columns and D1–D5 provisional rows, PROP-42/30/47/
    50/43 text, PROP-43 caller contract, `docs/signal-deviation-questions.md`.
    Closes the DEV-01..04 issues.
- **D-16:** Order: PR A first, then PR B. PR B's issues are filed with the
  script that PR A introduces (from the branch is acceptable, since PR B is
  filed after PR A's work is verified; if PR A has not merged, run the script
  from the PR A branch).
- **D-17:** `check_no_sorry`: remove the literal token from
  `docs/ISSUE_TEMPLATE.md`, `CLAUDE.md` and
  `docs/rubrics/spqr-plan-review.md`. The rubric and CLAUDE.md keep their
  warning, reworded as "a plan citing a gate that does not exist in the
  repository has a broken gate", so `grep -rn check_no_sorry` is clean.

### Claude's Discretion
- Whether `scripts/check-lint.sh` is renamed to `check-gates.sh`.
- Exact wording of the corrected template checklist, as long as it lists the
  four gates by command and a catalog-and-index update line.
- Layout of the issue script (bash with heredocs vs a small generator reading
  the catalog), as long as it is idempotent, dry-run by default and produces
  bodies matching `docs/ISSUE_TEMPLATE.md`.
- Where the gate script documents itself (`scripts/README.md` is the natural
  place).

</decisions>

<canonical_refs>
## Canonical References

**Downstream agents MUST read these before planning or implementing.**

### Catalog and process
- `docs/spqr-properties.md` §1 — verification setup, the opaque stubs that
  form the `#print axioms` allowlist, the hand-written sorries.
- `docs/spqr-properties.md` §5 PROP-42, §7 PROP-43, §8 PROP-30/47/50 — the
  property text that must state the provisional D1–D5 behaviour.
- `docs/spqr-properties.md` §11 — the deviation table that gains Decision and
  Status columns.
- `docs/spqr-properties.md` §12 — index; CAT-01 requires it to change with
  every theorem PR.
- `docs/ISSUE_TEMPLATE.md` — the template to correct (line 98 names the
  nonexistent `#check_no_sorry`); its Labels section is the label scheme.
- `docs/rubrics/spqr-plan-review.md` item 7 — the gate list Codex reviews
  against; mentions the `check_no_sorry` token (line 110).
- `CLAUDE.md` Constraints, "Gates" bullet — mentions the token; reword.

### Gates as CI runs them
- `.github/workflows/lean.yml` — build-warning check, lint, cached base
  manifest restore, `Audit.lean`, artifact upload. Not to be edited.
- `.github/workflows/sorry-delta-comment.yml` — how the delta is computed
  and posted.
- `scripts/check-lint.sh` — gates 1 and 2 as a local script; the file to
  extend.
- `scripts/Audit.lean` — axiom audit and `sorry-manifest.txt` writer; the
  header comment documents its four sections and the requirement that new
  modules be re-exported from `Spqr.lean`.
- `scripts/sorry-diff.py` — manifest comparison logic to reuse or call for
  the local delta.
- `scripts/README.md` — where the new script is documented.

### Issue tooling being replaced
- `issues/create_issues.sh` — old script with a divergent label scheme
  (`status:provable-now`, `tier:*`); replaced.
- `issues/SPQR_ISSUES_PREVIEW.md`, `issues/272/` — stale; deleted.
- GitHub issues #44 (umbrella, PROP-9,14,17,21,26,30,33,39) and #510–#533
  (per-function "Specify and verify" issues) — cross-linked, never edited.
- PRs #537–#541 — the PR body shape to follow ("This PR specifies and
  verifies … Closes #N").

### Project planning
- `.planning/REQUIREMENTS.md` — INFRA-02 to reword (D-09).
- `.planning/ROADMAP.md` Phase 1 — success criterion 3 to reword and "Plans:
  TBD (8 PR boundaries)" to become two.

</canonical_refs>

<code_context>
## Existing Code Insights

### Reusable Assets
- `scripts/check-lint.sh`: exact local copy of CI gates 1 and 2; extend
  rather than duplicate.
- `scripts/Audit.lean`: already computes the transitive axiom closure per
  `Spqr.Specs` theorem and writes `sorry-manifest.txt`; the local script only
  needs to run it in two trees and diff.
- `scripts/sorry-diff.py`: takes base and head manifests and reports new
  `Spqr.Specs` entries; honours `SORRY_FAIL_ON_NEW=true` for a non-zero exit.
- `docs/ISSUE_TEMPLATE.md`: complete issue body shape with type, source,
  difficulty, status, dependencies and labels; the issue script fills it.

### Established Patterns
- CI treats `declaration uses 'sorry'` as the only allowed warning and lints
  only the hand-written `Spqr` library.
- The base manifest in CI is keyed on the PR base SHA and cached from pushes
  to `main`; locally the same baseline is only obtainable by building `main`.
- Existing property PRs are one function per PR with a one-line body and a
  closing reference.

### Integration Points
- `lakefile.toml` default targets `Spqr` and `SrcTranslated`; the worktree
  build must use the same toolchain (`lean-toolchain`, pinned Aeneas rev).
- `.gitignore` already ignores `sorry-manifest.txt`; the cached main
  manifest and the worktree path need entries too.
- Label creation and issue filing need an authenticated `gh` in the repo
  `Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify`.

</code_context>

<specifics>
## Specific Ideas

- The user wants issues to exist only when there is a PR to close them:
  "when we're done with a PR we create the issue it can close and so on".
- The Signal note should be sendable as-is; each question ends with the two
  resolutions the catalog already names (code fix vs spec erratum for D1,
  strict vs no-op for D2, document vs drop for D3/D4, caller contract for D5).
- §11's existing sentence "Until decided, the properties above describe the
  code as it is" becomes the definition of Status = Provisional.

</specifics>

<deferred>
## Deferred Ideas

- Refactoring `lean.yml` to call the gate script so local and CI cannot
  drift. Rejected for this phase (D-08a); could be its own infra issue later.
- Extending `Audit.lean` with an allowlist check and non-zero exit for
  whole-project axiom coverage. Not needed for the per-PR grain; revisit if
  Phase 8's regeneration wants it.
- Closing or retitling #44 and Markus's per-function issues. Left to the
  user; GSD only cross-links.

</deferred>

---

*Phase: 01-gates-issues-and-deviation-decisions*
*Context gathered: 2026-09-14*
