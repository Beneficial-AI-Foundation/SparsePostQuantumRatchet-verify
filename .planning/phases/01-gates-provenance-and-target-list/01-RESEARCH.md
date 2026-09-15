# Phase 1: Gates, Provenance and the Reviewed Target List - Research

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


**Researched:** 2026-09-14
**Domain:** Repository process tooling (bash gate script, `gh` issue automation) and
Markdown catalog surgery. No Lean proofs, no `src/` change, no CI workflow change.
**Confidence:** HIGH (everything below is read off the working tree or a read-only
`gh`/`git`/`gsd-sdk` probe run in this session)

> **Notation.** Success criterion 1 requires `grep -rn <phantom>` over the repo to return
> nothing, where `<phantom>` is the non-existent gate token currently on
> `docs/ISSUE_TEMPLATE.md:98`. **This document never writes that token literally** — it would
> defeat the criterion the moment the research file is committed. It is called
> **PHANTOM-TOKEN** throughout. Plans, summaries and eval files for this phase must follow the
> same rule, or use the scoped grep recommended in Open Question Q-1.

---

## Summary

This is a three-strand phase with almost no shared surface: a bash gate runner, a `gh`
issue filer, and Markdown edits to `docs/spqr-properties.md`. All three are mechanical
once the facts are pinned. The facts are pinned below, read directly off the tree.

Six findings materially change what the plans must say, and four of them contradict an
assumption baked into CONTEXT.md or the ROADMAP. In descending order of blast radius:
`issues/` is **gitignored and untracked**, so "delete it in PR A" is not a diff and cannot
be a PR deliverable; **no `gsd-sdk` handler edits requirement or success-criterion text**,
so D-09's "go through `gsd-sdk` handlers, not direct edits" is not executable as written;
the PHANTOM-TOKEN appears in **nine** files, not the three D-17 names, and six of them are
tracked `.planning/` files, so criterion 1's unscoped grep fails unless the grep is scoped
or every planning artifact is reworded; and `main` **does not contain the catalog at all** —
`docs/spqr-properties.md`, `docs/ISSUE_TEMPLATE.md`, `docs/rubrics/`, `CLAUDE.md` and
`.planning/` are all new on the unmerged `la/spec-catalog` branch, which decides what PR A
and PR B are based on.

Two further facts constrain the gate script: `.lake/build` does not exist (the project is
currently **unbuilt**; only `.lake/packages` sources are present), and mathlib is a
transitive dependency via aeneas, so a `git worktree` baseline needs `lake exe cache get`
before `lake build` or it compiles mathlib from source. Separately, the local branch has
**zero** Lean-file differences from `origin/main`, so for Phase 1 itself the sorry-delta
gate is trivially clean — the script must still be correct in general, but it cannot be
validated against a real delta without deliberately introducing one.

**Primary recommendation:** Split PR A into a *gate* strand and an *issues* strand inside one
PR, write the gate runner as a new `scripts/check-gates.sh` that keeps `check-lint.sh` as a
two-line shim, write the issue filer as a bash script with a data table keyed by property ID
and `gh issue create --body-file`, and treat the four blockers above as planner decisions to
be recorded explicitly rather than discovered during execution.

---

<user_constraints>
## User Constraints (from CONTEXT.md)

### Locked Decisions

**Issue set and labels**
- **D-01:** GSD files issues itself with `gh issue create`. Issues are not PRs, so the "user
  opens every PR" rule is untouched. The user reviews a dry-run listing (title + labels)
  before anything is filed.
- **D-02:** Fresh per-property issues. Each body cross-links overlapping per-function issues
  (#510–#533) and the umbrella #44 as "related". GSD does not close, retitle or relabel any
  existing issue.
- **D-03:** Label scheme is the template's: `type:*` and
  `status:open | status:axiom | status:proved-branch | status:proved`, created once by an
  idempotent step. Catalog status and issue label stay one-to-one. Repo labels `Proof`,
  `Specification`, `Infrastructure`, `Sorry` are not used for these issues.
- **D-04:** Every deliverable that lands via a PR gets an issue: property rows and also INFRA,
  MERGE-04..07, AXIOM, DEV and CAT requirements. Non-property issues use `type:proof-infra`
  or `spec-deviation`.
- **D-05:** A new idempotent script (labels + issue bodies from the template, dry-run by
  default, `--execute` to file) replaces `issues/create_issues.sh`.
  `issues/SPQR_ISSUES_PREVIEW.md` and `issues/272/` are deleted in the same PR. One source of
  truth for issue bodies.

**Local gate check**
- **D-06:** Extend `scripts/check-lint.sh`, which already runs gates 1 and 2 byte-for-byte as
  `.github/workflows/lean.yml`, with three further sections:
  `lake env lean scripts/Audit.lean`, a sorry-manifest delta, and `#print axioms`. Renaming to
  `check-gates.sh` with a compatibility note is the planner's call.
- **D-07:** Baseline for the sorry-manifest delta: the script creates or updates a git
  worktree at `origin/main`, runs `Audit.lean` there once and caches the resulting manifest
  under a gitignored path. This reproduces CI's cached-main-manifest comparison exactly. First
  run costs a full build of `main`.
- **D-08:** `#print axioms` targets are theorem names passed as script arguments. The script
  writes a scratch Lean file with one `#print axioms` per name and greps the output against
  the allowlist: `propext`, `Classical.choice`, `Quot.sound` and the documented stubs of
  catalog §1. No change to `Audit.lean`.
- **D-08a:** Local only. `lean.yml` is not modified. Success criterion 2 is met by running the
  script on `main` and comparing with CI's result.

**Issue timing and INFRA-02 rewording**
- **D-09:** Issues are filed just-in-time, not in a batch. When a PR's work is complete and
  verified, GSD runs the issue script for that single deliverable, then stops at the PR
  boundary and reports the issue number so the user opens the PR with `Closes #N`.
  Consequences, to be applied by the planner in the same phase:
  - INFRA-02 is reworded to: "A repeatable script files one issue per property from the
    corrected template; each PR's issue is created at its PR boundary, before the user opens
    the PR."
  - Success criterion 3 of Phase 1 drops the "one open issue per v1 property" count; it
    becomes "the issue script files a correctly labelled issue from the template, demonstrated
    on the Phase 1 issues".
  - The roadmap references property IDs, not issue numbers, in later phases.
  - REQUIREMENTS.md and ROADMAP.md changes go through `gsd-sdk` handlers, not direct edits.

**D1–D5 without a Signal ruling**
- **D-10:** A "recorded decision" while Signal is silent is `Status = Provisional`,
  `Decision = code as implemented is authoritative`. Properties are stated against the code
  now. Phase 1 does not wait on Signal. A later ruling flips Status to Decided with a date
  and, if it disagrees with the code, opens a restatement issue for the affected property.
- **D-11:** GSD drafts `docs/signal-deviation-questions.md`: five questions, each with the spec
  text, the code lines, the impact and the two candidate resolutions, ready to send. The user
  sends it through their own channel. Answers are pasted back into §11.
- **D-12:** §11 keeps its single table and gains two columns: `Decision` and `Status`
  (Provisional / Decided, with date). No per-deviation subsections.
- **D-13:** D5's caller contract (MAC failure returns `Err`, the caller keeps the previous
  state and may retry, the library does not abort the session) is written out in catalog §7
  under PROP-43. §11 row D5 points to it. The AUTH-01 theorem in Phase 5 quotes it.
- **D-14:** The catalog text for PROP-30, PROP-47, PROP-50 and PROP-43 is reviewed so each
  states the provisional behaviour explicitly and cites the D-row (D2, D3/D4, D5) so Phases
  5–6 can quote it verbatim. PROP-42 §5 is aligned with the D1 provisional decision.

**PR grouping and order**
- **D-15:** Two PR boundaries, not eight:
  - PR A (infra): template fix, CAT-01 checklist line, extended gate script, issue script and
    label creation, removal of `issues/`, PHANTOM-TOKEN rewording. Closes the INFRA-01/02/03
    and CAT-01 issues.
  - PR B (deviations): §11 columns and D1–D5 provisional rows, PROP-42/30/47/50/43 text,
    PROP-43 caller contract, `docs/signal-deviation-questions.md`. Closes the DEV-01..04
    issues.
- **D-16:** Order: PR A first, then PR B. PR B's issues are filed with the script that PR A
  introduces (from the branch is acceptable, since PR B is filed after PR A's work is
  verified; if PR A has not merged, run the script from the PR A branch).
- **D-17:** PHANTOM-TOKEN: remove the literal token from `docs/ISSUE_TEMPLATE.md`, `CLAUDE.md`
  and `docs/rubrics/spqr-plan-review.md`. The rubric and CLAUDE.md keep their warning,
  reworded as "a plan citing a gate that does not exist in the repository has a broken gate",
  so the repo-wide grep is clean.

### Claude's Discretion
- Whether `scripts/check-lint.sh` is renamed to `check-gates.sh`.
- Exact wording of the corrected template checklist, as long as it lists the four gates by
  command and a catalog-and-index update line.
- Layout of the issue script (bash with heredocs vs a small generator reading the catalog), as
  long as it is idempotent, dry-run by default and produces bodies matching
  `docs/ISSUE_TEMPLATE.md`.
- Where the gate script documents itself (`scripts/README.md` is the natural place).

### Deferred Ideas (OUT OF SCOPE)
- Refactoring `lean.yml` to call the gate script so local and CI cannot drift. Rejected for
  this phase (D-08a); could be its own infra issue later.
- Extending `Audit.lean` with an allowlist check and non-zero exit for whole-project axiom
  coverage. Not needed for the per-PR grain; revisit if Phase 8's regeneration wants it.
- Closing or retitling #44 and Markus's per-function issues. Left to the user; GSD only
  cross-links.
</user_constraints>

---

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|------------------|
| INFRA-01 | Template checklist names the real gates instead of the PHANTOM-TOKEN | §"Gate mechanics" gives all four gate commands verbatim; §"PHANTOM-TOKEN inventory" enumerates all nine hits (D-17 named only three) |
| INFRA-02 | A GitHub issue exists per property, from the template, labelled, referenced from the roadmap phase (reworded by D-09) | §"Issue script" gives the template field set, the label gap (`type:*`/`status:*` do not exist in the repo), the idempotent `gh` invocations, and the confirmed auth; Blocker B-2 shows the D-09 rewording route is a manual edit, not a handler |
| INFRA-03 | A repeatable local check reproduces CI's build, lint and sorry-manifest gates | §"Gate mechanics" gives byte-for-byte CI equivalence, the `sorry-diff.py` CLI, the worktree recipe, and the `#print axioms` allowlist |
| CAT-01 | Every theorem PR updates status, section text and §12 index | §"Catalog surgery" gives the §12 row format and the exact template checklist line to add |
| DEV-01 | D1 recorded decision; PROP-42 §5 matches | §"Catalog surgery" quotes the current D1 row and the PROP-42 paragraph verbatim |
| DEV-02 | D2 recorded decision; PROP-30 and PROP-50 stated for it | quotes the D2 row, the PROP-30 dispatch table and the PROP-50 paragraph |
| DEV-03 | D3/D4 recorded decisions; PROP-47 transition table matches | quotes D3/D4 rows and PROP-47 rows 11/12 plus the trailing status paragraph |
| DEV-04 | D5 written caller contract; PROP-43 stated against it | quotes the D5 row, the PROP-43 paragraph, and gives the `src/` line evidence for the contract |

</phase_requirements>

---

## Project Constraints (from CLAUDE.md)

Actionable directives extracted from `CLAUDE.md` (and `.planning/PROJECT.md`, which carries
the same constraint block). Plans must comply; the plan reviewer checks these.

| # | Directive | Effect on this phase |
|---|-----------|----------------------|
| PC-1 | **Code freeze**: `src/` changes limited to agreed D1–D5 resolutions | Phase 1 records *provisional* decisions only (D-10). **No `src/` edit at all.** Any diff hunk under `src/` is a BLOCKER for both the plan reviewer (rubric item 8) and `spqr-eval`. |
| PC-2 | **Never hand-edit `SrcTranslated/`** | Not touched. The gate script must not write there. |
| PC-3 | **No toolchain bumps inside a property PR** | The gate script must not change `lean-toolchain`, `lakefile.toml` or `lake-manifest.json`; the worktree must inherit the same pinned toolchain. |
| PC-4 | **Trusted base**: no new hand-written axiom without a catalog entry | No axioms added this phase. The gate-4 allowlist *documents* the existing ones; it must not silently widen them. |
| PC-5 | **Provenance**: theorem statements match catalog wording; changing a statement changes the catalog in the same PR | PR B changes catalog wording *before* any theorem exists — the right order. Plans for phases 5–6 will quote it. |
| PC-6 | **The user opens every PR.** GSD stops at the PR boundary and reports. | Both PR A and PR B end with a STOP-and-report task. GSD may create *issues* (D-01) but never a PR. |
| PC-7 | **Review gates**: `/spqr-plan-review 1` after planning, before execution; `spqr-eval` after execution, persisted as `01-EVAL.md` | See §"Review gates". Rubric item 7 is directly about this phase's subject matter. |
| PC-8 | Markdown filenames in **kebab-case**, except conventional all-caps (`README.md`, `CLAUDE.md`, …) | `docs/signal-deviation-questions.md` ✓. Note `docs/ISSUE_TEMPLATE.md` is *not* an all-caps convention name — but it is pre-existing and referenced from `CLAUDE.md`, `PROJECT.md` and the ROADMAP; **do not rename it** in this phase (out of scope, and it would break five references). |
| PC-9 | GSD workflow enforcement: no direct repo edits outside a GSD workflow | All edits land through `/gsd:execute-phase 1`. |
| PC-10 | Gates are `lake build` (no non-sorry warning), `lake exe runLinter Spqr`, `lake env lean scripts/Audit.lean`, `#print axioms` | Exactly the four the gate script must run. |

---

## Architectural Responsibility Map

There is no application tier stack here. The equivalent axis is *which artifact owns which
guarantee*, which is what the plan reviewer checks under rubric items 2 and 7.

| Capability | Primary owner | Secondary owner | Rationale |
|------------|---------------|-----------------|-----------|
| Build-warning gate (gate 1) | `.github/workflows/lean.yml` (authoritative) | `scripts/check-gates.sh` (local mirror) | CI is the merge gate; local must be byte-for-byte identical or the "matches CI" criterion is unverifiable |
| Lint gate (gate 2) | `lean.yml` | `scripts/check-gates.sh` | same |
| Axiom audit + manifest generation (gate 3a) | `scripts/Audit.lean` | — | single implementation, run by both CI and local; **D-08 forbids changing it** |
| Manifest delta (gate 3b) | `scripts/sorry-diff.py` | `scripts/check-gates.sh` supplies the two manifests | CI's delta lives in `sorry-delta-comment.yml`; the local script must *call* `sorry-diff.py`, not reimplement it |
| Baseline manifest for the delta | GitHub Actions cache (CI) / git worktree at `origin/main` (local) | — | the only two ways to get a `main` manifest; they are different mechanisms with the same output |
| Per-theorem trusted base (gate 4) | scratch Lean file + allowlist in `check-gates.sh` | catalog §1 (the allowlist's source of truth) | `#print axioms` is a Lean command, not a lake target; there is no CI step for it today |
| Issue body content | `docs/ISSUE_TEMPLATE.md` | `scripts/create-property-issues.sh` fills it | D-05: one source of truth |
| Label taxonomy | `docs/ISSUE_TEMPLATE.md` "Labels" section | the issue script's idempotent create step | D-03 |
| Property statements | `docs/spqr-properties.md` | Lean theorems (phases 2–7) | PC-5: catalog is the contract |
| Deviation decisions | `docs/spqr-properties.md` §11 | `docs/signal-deviation-questions.md` (the outgoing ask) | D-12: single table, no subsections |
| Requirement / success-criterion text | `.planning/REQUIREMENTS.md`, `.planning/ROADMAP.md` | — | **no tool owns editing these** (Blocker B-2) |

---

## Blockers and corrections to CONTEXT.md assumptions

These five are the highest-value output of this research. Each contradicts something a plan
would otherwise assume. **Every one is verified in this session.**

### B-1 — `issues/` is gitignored and untracked; "delete it in PR A" is not a diff

`.gitignore:25` contains a bare `issues/` line. Verified:

```
$ git check-ignore -v issues/create_issues.sh issues/SPQR_ISSUES_PREVIEW.md issues/272/README.md
.gitignore:25:issues/	issues/create_issues.sh
.gitignore:25:issues/	issues/SPQR_ISSUES_PREVIEW.md
.gitignore:25:issues/	issues/272/README.md

$ git ls-files issues/ | wc -l
0
```

[VERIFIED: `git check-ignore`, `git ls-files`]

Consequences for the plan:
1. "Remove `issues/` in PR A" produces **no hunk**. A verifier checking the PR A diff for the
   deletion will not find it. The task must be stated as a *local filesystem* action with a
   filesystem verification (`test ! -e issues/`), not a git one.
2. The `.gitignore:25` `issues/` line is the only tracked artifact related to the directory.
   Deleting the directory leaves a dangling ignore rule. Recommend: **remove the
   `issues/` line from `.gitignore` in PR A** — that *is* a real hunk, it is the reviewable
   evidence that the old tooling is retired, and it prevents a future `issues/` directory from
   being silently ignored.
3. `issues/272/` currently contains **only** `README.md`; the seven `.lean` files its table
   describes (`Refutation.lean`, `FrameFix.lean`, …) are already gone. The README references
   `lake env lean issues/272/<File>.lean`, which cannot work. Nothing else in the repo
   references `issues/272/`.
4. Nothing under `scripts/`, `.github/`, `docs/` or `package.json` references any `issues/`
   path. The `grep -rn "issues/"` hits are all GitHub *URLs* (`.../issues/104`) in
   `aeneas-config.yml` and one external URL in `docs/report-consistency-check.md` — unrelated.
   [VERIFIED: repo-wide grep over `*.md,*.sh,*.yml,*.json,*.py,*.ts`]
5. The new issue script must therefore live **outside** `issues/` (which would be ignored).
   Put it under `scripts/`.

### B-2 — No `gsd-sdk` handler edits requirement or success-criterion text

D-09 says "REQUIREMENTS.md and ROADMAP.md changes go through `gsd-sdk` handlers, not direct
edits." No such handler exists. Verified against the installed SDK
(`~/.npm/_npx/4db0de1f85c3165e/node_modules/get-shit-done-cc`, `gsd-sdk` → `gsd-tools.cjs`):

```
$ gsd-tools requirements
Error: Unknown requirements subcommand. Available: mark-complete

$ gsd-tools roadmap
Error: Unknown roadmap subcommand. Available: analyze, get-phase, update-plan-progress, annotate-dependencies
```

The SDK's native registry agrees — the only registered commands in these families are
`requirements.mark-complete`, `roadmap.analyze`, `roadmap.get-phase`,
`roadmap.update-plan-progress`, `roadmap.annotate-dependencies`
(`sdk/src/query/command-manifest.roadmap.ts`, `command-manifest.non-family.ts`).
`requirements mark-complete REQ-01,REQ-02` only ticks the `- [ ]` checkbox
(`get-shit-done/bin/lib/milestone.cjs:15`).
[VERIFIED: CLI probe + SDK source]

**Recommendation for the planner:** state explicitly in the plan that the INFRA-02 rewording
and the criterion-3 rewording are **manual `Edit` operations** on `.planning/REQUIREMENTS.md`
and `.planning/ROADMAP.md`, performed as part of PR A, preserving:
- the `- [ ] **INFRA-02**: …` bullet shape (the `mark-complete` handler parses it);
- the numbered `  1.` … `  5.` indentation of the ROADMAP success-criteria list
  (`roadmap.get-phase` parses it — confirm with `gsd-sdk query roadmap.get-phase 1` after the
  edit);
- the `**Plans**: TBD (…)` line, updated to two PR boundaries per D-15.

Add a verification task: `gsd-sdk query roadmap.get-phase 1` must still return the phase with
its criteria after the edit.

### B-3 — The PHANTOM-TOKEN appears in nine files, not three; criterion 1 is unachievable as written

D-17 names three files. The repo-wide grep finds nine (excluding `.git`, `.lake`,
`node_modules`):

| File:line | Tracked? | In D-17? |
|-----------|----------|----------|
| `docs/ISSUE_TEMPLATE.md:98` | yes | yes |
| `docs/rubrics/spqr-plan-review.md:110` | yes | yes |
| `CLAUDE.md:24` | yes | yes |
| `.planning/PROJECT.md:67` | yes | **no** |
| `.planning/STATE.md:66` | yes | **no** |
| `.planning/REQUIREMENTS.md:15` | yes | **no** |
| `.planning/ROADMAP.md:56` | yes | **no** |
| `.planning/phases/01-…/01-CONTEXT.md:105,114,118,147,149` | yes | **no** |
| `.planning/phases/01-…/01-DISCUSSION-LOG.md:159` | yes | **no** |

`.planning/` **is tracked** (`git ls-files .planning` → 7 files, all of them new on this
branch). [VERIFIED: `grep -rn`, `git ls-files`]

So an unscoped `grep -rn` cannot return empty while the phase's own CONTEXT and DISCUSSION-LOG
exist — and it would also fail the moment a plan file, summary or eval mentions the token.
Rewriting the CONTEXT/DISCUSSION-LOG of a completed discussion session is not desirable
(they are the record of *why* the token is being removed).

See Open Question Q-1 for the recommended resolution.

### B-4 — `main` has no catalog; the PR base is not obvious

`git diff --stat origin/main..HEAD` is 14 files, **2229 insertions, 0 deletions**. Every file
this phase edits is new on `la/spec-catalog` and absent from `origin/main`
(`d47083cd3abf2906229efa38ae2bfb1121498af0`, 2026-09-14):

`docs/spqr-properties.md`, `docs/ISSUE_TEMPLATE.md`, `docs/rubrics/spqr-plan-review.md`,
`CLAUDE.md`, `.planning/**`, `.claude/agents/spqr-eval.md`,
`.claude/skills/spqr-plan-review/SKILL.md`, `.gitignore` (+10 lines).
[VERIFIED: `git diff --stat origin/main..HEAD`]

Consequences:
- PR A and PR B cannot be "small docs PRs against `main`" unless `la/spec-catalog` merges
  first, because their diffs would include the whole catalog.
- STATE.md already records: "Local `la/spec-catalog` has diverged from `origin/la/spec-catalog`;
  pushing needs `--force-with-lease`."
- The plan must record a base decision. Recommended: branch PR A from `la/spec-catalog`
  (`gsd/phase-1a-gates-and-issues`) and target `la/spec-catalog`, with PR B stacked on PR A.
  This is a **user decision** — surface it at the first PR boundary report rather than
  assuming it. Note `.planning/config.json` has `git.branching_strategy: "none"`, so GSD will
  not create a branch on its own.
- Zero `*.lean`, `lakefile.toml` or `lean-toolchain` differences vs `origin/main`. The gate
  script's sorry-delta will therefore be empty on this branch — correct, but it means the
  delta path is **not exercised** by a normal Phase 1 run. See Validation Architecture.

### B-5 — The project is currently unbuilt; a worktree baseline needs the mathlib cache

```
$ find .lake/build -name '*.olean' | wc -l       →  (no .lake/build directory at all)
$ ls .lake/                                      →  config  packages  probe-lean
$ du -sh .lake/packages                          →  819M
$ for d in .lake/packages/*/; do … done          →  aeneas 1, mathlib 1, proofwidgets 1, rest 0 oleans
```

[VERIFIED: filesystem probe]

`lake-manifest.json` pulls in `aeneas, mathlib, plausible, LeanSearchClient, importGraph,
proofwidgets, aesop, Qq, batteries, Cli`. Mathlib is transitive via aeneas — which is also
where `lake exe runLinter` comes from (`batteries/lakefile.toml:22` defines the `runLinter`
exe; `mathlib/lakefile.lean:51` sets `lintDriver := "batteries/runLinter"`).
[VERIFIED: lakefiles]

So:
- CI gets mathlib oleans from `leanprover/lean-action@v1` with `use-mathlib-cache: true`
  (`lean.yml:41-46`).
- Locally, **both** the main tree and any worktree must run `lake exe cache get`
  (`mathlib/lakefile.lean:101` defines the `cache` exe) before `lake build`, or mathlib
  compiles from source (hours, not minutes).
- A `git worktree` gets a *fresh, empty* `.lake/`. Cold first run = `lake exe cache get`
  (network, GB-scale download) + `lake build` of aeneas backend + `SrcTranslated` + `Spqr`.
  Budget for this in the plan's task estimates and make the script print a loud warning
  before it starts.
- Disk: 415G free. Not a constraint.

---

## Gate mechanics (INFRA-03, D-06 / D-07 / D-08)

### The four gates, exactly as CI runs them

| # | Gate | CI step (`.github/workflows/lean.yml`) | Command | Failure convention |
|---|------|----------------------------------------|---------|--------------------|
| 1 | Build warnings | "Build and check for non-sorry warnings" (L48–55) | `lake build --no-ansi 2>&1 \| tee /tmp/lake-build.log` then `grep 'warning:' … \| grep -qv 'declaration uses .sorry'` | `exit 1` if any warning line survives the `grep -v` |
| 2 | Lint | "Lint hand-written code" (L57–65) | `lake exe runLinter Spqr 2>&1 \| tee /tmp/lake-lint.log \|\| true` then `grep -q 'error:' /tmp/lake-lint.log` | `exit 1` if any `error:` line. Note the `\|\| true`: the linter's own exit code is **ignored**; only the log grep decides. |
| 3 | Axiom audit + manifest | "Axiom audit and sorry manifest" (L77–78) | `lake env lean scripts/Audit.lean` | plain lake/lean exit code. CI does **not** assert anything about the output; it only regenerates `sorry-manifest.txt`. |
| 3b | Manifest delta | `sorry-delta-comment.yml` (L39–41) | `python3 scripts/sorry-diff.py <base> <head>` | exit 0 unless `SORRY_FAIL_ON_NEW=true` **and** new `Spqr.Specs.*` lines exist → exit 1 |
| 4 | Per-theorem trusted base | **no CI step exists** | `#print axioms <thm>` in a scratch Lean file | invented by this phase; see below |

[VERIFIED: `.github/workflows/lean.yml`, `.github/workflows/sorry-delta-comment.yml`,
`scripts/check-lint.sh`, `scripts/sorry-diff.py`]

`scripts/check-lint.sh` already reproduces gates 1 and 2 **byte-for-byte** (same commands,
same log paths `/tmp/lake-build.log` and `/tmp/lake-lint.log`, same greps), differing only in
printing `FAIL:`/`PASS` instead of `::error::`. Keep it that way: any drift breaks criterion 2.
Note the `LEAN_ABORT_ON_PANIC=1` env var CI sets at workflow level (`lean.yml:22-23`) — the
local script should export it too for exact equivalence.

### What `Audit.lean` emits and where

`lake env lean scripts/Audit.lean` runs a `run_cmd` over the environment reachable from
`import Spqr` and logs four sections to **stdout** (Lean `logInfo`), then writes one file:

- **Section 1** — per-`Spqr.Specs.*` theorem/axiom, the non-builtin axiom closure.
  Builtin = `propext`, `Classical.choice`, `Quot.sound` (`Audit.lean:26-27`,
  `isBuiltinAxiom`).
- **Section 2** — for each sorry-tainted spec, a BFS path to the declaration whose own body
  contains `sorryAx`.
- **Section 3** — whole-project (`Spqr.*` + `SrcTranslated.*`) summary counts.
- **Section 4** — writes `sorry-manifest.txt` **into the current working directory**
  (`IO.FS.writeFile "sorry-manifest.txt"`, `Audit.lean` end). Relative path — so the worktree
  run produces the worktree's own file, which is what we want.

`Audit.lean` **never exits non-zero** on findings. It only fails if Lean fails to elaborate.
The header also states the load-bearing constraint the plan reviewer checks (rubric item 2):
*"Any `Spqr.*` module not imported by the root `Spqr` module will not be scanned. Ensure new
modules are re-exported from `Spqr.lean`."*

**`sorry-manifest.txt` format** — one line per sorry-tainted declaration, space-separated,
sorted lexicographically, trailing newline:

```
<module> <declaration> <kind>
```

`<kind>` ∈ `direct` | `transitive`. Real lines from the current file:

```
Spqr.Specs.Aeneas.MapCollectBridge Spqr.Aeneas.collect_default_bridge direct
Spqr.Specs.Encoding.Encoder.EncodeBytes spqr.core.option.Option.Insts.SpqrEncodingEncoder.encode_bytes_spec_poly_encoder transitive
SrcTranslated.Funs spqr.recv transitive
SrcTranslated.Funs spqr.send transitive
SrcTranslated.Funs spqr.initial_state transitive
```

Current file: **134 lines total, 36 of them `Spqr.Specs.*`**. It is gitignored
(`.gitignore:31`) and the working copy is dated 2026-08-07 — **treat it as stale**; the gate
script must regenerate it, never read the checked-out one as a baseline.
[VERIFIED: `sorry-manifest.txt`, `.gitignore`]

### `sorry-diff.py` CLI (call it, do not reimplement)

```
python3 scripts/sorry-diff.py <base-manifest> <head-manifest>
```

- **Positional order matters**: base first, head second. `argv[1]`=base, `argv[2]`=head.
- Exits 1 immediately if fewer than 2 args, or if the **head** manifest is missing.
- A **missing base** is not an error: `read_manifest` returns `{}` for a nonexistent path and
  the script prints `No baseline available for comparison.` and reports zero new lines. So the
  local script can call it before the baseline exists and get a clean, honest "no baseline"
  run.
- Identity key is the **declaration name only** (`parts[1]`), not the whole line.
- "specs" means module `== "Spqr.Specs"` or starting with `"Spqr.Specs."`.
- Env vars, all optional:
  - `SORRY_FAIL_ON_NEW=true` → `sys.exit(1)` when new specs lines exist. **Set this in the
    local gate script** — that is the whole point of a local gate.
  - `GITHUB_STEP_SUMMARY` → appends two summary lines to that path. Leave unset locally.
  - `GITHUB_OUTPUT` → appends `post_comment=true|false`. Leave unset locally.
- Side effect: writes `.sorry-delta-comment.md` in the CWD **only when** new specs lines exist.
  Locally this is a stray file — `.gitignore` it, or `rm -f` it after the call.
- Stdout is the useful local output: a `--- Sorry Delta Summary ---` block plus one
  `⚠  [module] decl (kind)` line per new specs entry.

[VERIFIED: `scripts/sorry-diff.py` read in full]

### Baseline worktree recipe (D-07), concrete

There is precedent for sibling worktrees: `git worktree list` already shows
`/home/lacra/git_repos/baif/spqr-pr340` (detached at `acee47a`) alongside the main checkout.
Follow it — put the baseline worktree **outside the repo tree** so no `.gitignore` entry is
needed for it. [VERIFIED: `git worktree list`]

```bash
# Configurable, with sane defaults.
BASELINE_REF="${SPQR_BASELINE_REF:-origin/main}"
WT_DIR="${SPQR_BASELINE_WORKTREE:-$(cd "$REPO_ROOT/.." && pwd)/spqr-gate-baseline}"
CACHE_DIR="${SPQR_GATE_CACHE:-$REPO_ROOT/.gate-cache}"

git -C "$REPO_ROOT" fetch --quiet origin main
BASE_SHA="$(git -C "$REPO_ROOT" rev-parse "$BASELINE_REF")"
BASE_MANIFEST="$CACHE_DIR/sorry-manifest-$BASE_SHA.txt"

if [[ ! -f "$BASE_MANIFEST" ]]; then
  echo "=== Cold baseline build for $BASELINE_REF ($BASE_SHA) — this takes a while ==="
  if [[ ! -d "$WT_DIR" ]]; then
    git -C "$REPO_ROOT" worktree add --detach "$WT_DIR" "$BASE_SHA"
  else
    git -C "$WT_DIR" checkout --detach "$BASE_SHA"
  fi
  ( cd "$WT_DIR"
    lake exe cache get            # mathlib oleans; without this, mathlib builds from source
    lake build --no-ansi
    lake env lean scripts/Audit.lean )
  mkdir -p "$CACHE_DIR"
  cp "$WT_DIR/sorry-manifest.txt" "$BASE_MANIFEST"
fi
```

Design notes:
- **Keyed by SHA**, so the cache self-invalidates when `origin/main` moves — exactly CI's
  cache key shape (`sorry-manifest-main-${{ github.sha }}`, `lean.yml:80-84`).
- The worktree is reused across refreshes (`checkout --detach`) so its `.lake` survives and
  only the changed modules rebuild.
- `--detach` avoids "branch already checked out" errors.
- **`.gitignore` additions needed: `.gate-cache/` and `.sorry-delta-comment.md`.**
  `sorry-manifest.txt` is already ignored (`.gitignore:31`). The worktree itself is outside
  the repo and needs no entry.
- Provide a `--skip-baseline` / `--no-delta` flag. On a machine with no baseline and no
  appetite for a cold build, the script should still run gates 1, 2, 3 and 4 and report the
  delta as SKIPPED — a partial gate run that says so is more useful than a script nobody runs.
- Provide `--refresh-baseline` to force a rebuild.
- **Cold-run cost is unmeasured in this session** (the tree is unbuilt, and building it was
  out of scope for read-only research). Plan a task to measure and record it in
  `scripts/README.md`. Order of magnitude: `lake exe cache get` downloads GB-scale mathlib
  oleans; `lake build` then compiles aeneas's Lean backend, `SrcTranslated/Funs.lean`
  (≈14k lines) and all of `Spqr/`. Expect tens of minutes on a warm cache, hours without.

### Gate 4: `#print axioms` recipe and allowlist

`#print axioms` is a Lean command, not a lake target. The D-08 approach — generate a scratch
file, elaborate it with `lake env lean`, grep the output — is the right one.

```bash
SCRATCH="$(mktemp -d)/PrintAxioms.lean"
{ echo 'import Spqr'
  for thm in "$@"; do echo "#print axioms $thm"; done
} > "$SCRATCH"
lake env lean "$SCRATCH" 2>&1 | tee /tmp/lake-axioms.log
```

Output shapes to handle (both must be accepted):
- `'<name>' depends on axioms: [propext, Classical.choice, Quot.sound]`
- `'<name>' does not depend on any axioms`

and one to reject loudly: `unknown identifier '<name>'` / `unknown constant` — a typo'd
theorem name must **fail** the gate, not pass it vacuously. This is the single most important
detail in gate 4: a name-typo that silently passes is worse than no gate.

**The allowlist.** Builtins plus catalog §1's documented opaque items. Fully-qualified Lean
names, read off the tree:

| Allowed name | Why | Source |
|---|---|---|
| `propext` | builtin | `Audit.lean:26` |
| `Classical.choice` | builtin | `Audit.lean:26` |
| `Quot.sound` | builtin | `Audit.lean:27` |
| `spqr.kdf.hkdf_to_slice_spec` | the single hand-written axiom | `Spqr/Specs/Kdf/HkdfToSlice.lean:25`, inside `namespace spqr.kdf` |
| `libcrux_ml_kem.mlkem768.incremental.validate_pk_bytes` | libcrux stub | `SrcTranslated/FunsExternal.lean:1985` |
| `libcrux_ml_kem.mlkem768.incremental.encapsulate1` | libcrux stub | `FunsExternal.lean:1994` |
| `libcrux_ml_kem.mlkem768.incremental.encapsulate2` | libcrux stub | `FunsExternal.lean:1856` |
| `libcrux_ml_kem.mlkem768.incremental.decapsulate_compressed_key` | libcrux stub | `FunsExternal.lean:2006` |
| `libcrux_ml_kem.mlkem768.incremental.pk1_len` / `.pk2_len` / `.encaps_state_len` | libcrux constants | `FunsExternal.lean:1838,1844,1850` |
| `libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.from_seed_spec` | libcrux stub spec | `FunsExternal.lean:1873` |
| `libcrux_ml_kem.constants.SHARED_SECRET_SIZE` | libcrux constant | `FunsExternal.lean:1806` |
| `libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1.len` / `Ciphertext2.len` | libcrux stubs | `FunsExternal.lean:1823,1831` |
| `libcrux_hmac.hmac` | libcrux HMAC stub | `FunsExternal.lean:1748` |
| `libcrux_hmac.hmac_sha256_tag32_spec` | libcrux HMAC stub spec | `FunsExternal.lean:1795` |
| `encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message` | catalog §1 stub, blocks LEAN-ENC-2 | `FunsExternal.lean:3682` |
| `incremental_mlkem768.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275` | catalog §1 stub | `FunsExternal.lean:3685` |
| `encoding.gf.mul2_u16` | SIMD dispatch, explicitly out of scope in REQUIREMENTS.md | `FunsExternal.lean:3676` |
| `sorryAx` | **conditionally**: only for theorems the catalog records as depending on the prost `sorry`s | see below |

Three traps in this list — call them out in the plan:

1. **`FunsExternal.lean` names are NOT `spqr.`-prefixed.** The file has `open spqr` (L16), not
   `namespace spqr`. So the axioms are root-level `libcrux_ml_kem.…`,
   `encoding.polynomial.…`, `incremental_mlkem768.…`, while `Funs.lean` declarations live in
   `namespace spqr` (L26) and appear as `spqr.recv`, `spqr.send`, `spqr.initial_state` in the
   manifest. The **only** `FunsExternal` declaration inside a namespace is
   `spqr.kdf.hkdf_to_slice` (`namespace spqr.kdf`, L3661–3672). Getting a prefix wrong makes
   an allowlist entry dead and the gate falsely strict. [VERIFIED: `FunsExternal.lean`,
   `Funs.lean:26`; this matches the recorded memory note "aeneas opaque lean-name prefix
   mismatch"]
2. **`opaque` declarations never appear in `#print axioms`.** `spqr.kdf.hkdf_to_slice`
   (`FunsExternal.lean:3669`) and `Spqr.Crypto.Hkdf`'s `HMAC_SHA256`
   (`Spqr/Crypto/Hkdf.lean:30`) are `opaque`, not `axiom` — Lean's `collectAxioms` only
   gathers `axiomInfo`. Only the *spec axiom* `spqr.kdf.hkdf_to_slice_spec` shows up. Listing
   the `opaque` names in the allowlist is harmless but misleading; document them as
   "opaque, invisible to `#print axioms`".
3. **`FunsExternal.lean` also declares bare `axiom initial_state`, `axiom send`, `axiom recv`
   at root** (L3694, L3700, L3708) — these are *dead template leftovers*. The real functions
   are `def initial_state` / `def send` / `def recv` inside `namespace spqr` in `Funs.lean`
   (L10830, L12978, L14378), and it is those that reach the manifest as
   `SrcTranslated.Funs spqr.recv transitive`. Do **not** allowlist the bare names; a theorem
   depending on them would be depending on the wrong constant. [VERIFIED: grep of both files
   plus manifest lines 61,124,125]

On `sorryAx`: a theorem whose closure contains `sorryAx` is exactly what gate 3b catches. Gate
4 should therefore **reject `sorryAx` by default** and require an explicit
`--allow-sorry <thm>` opt-in for the catalog's two known hand-written sorries
(`Spqr/Specs/Aeneas/MapCollectBridge.lean:70`, `Spqr/Specs/Lib/DecodeState.lean:54`) and the
prost-dependent rows (PROP-37, PROP-38). AXIOM-04/AXIOM-05 in Phase 4 will formalise that set.

**Keep the allowlist in one place.** Recommend a plain-text sidecar,
`scripts/axiom-allowlist.txt`, one name per line, `#` comments allowed, read by
`check-gates.sh`. Rationale: catalog §1 is the source of truth in prose, but a grep-able file
lets phases 2–7 diff the allowlist in review, and the Phase 4 AXIOM-01..06 work will edit it.
A hard-coded bash array hides that diff.

### Recommendation on the rename (Claude's discretion)

**Rename to `scripts/check-gates.sh`, keep `scripts/check-lint.sh` as a 3-line shim.**

Reasons: the file will no longer be about linting; `check-lint.sh` is referenced in CONTEXT.md
and possibly in contributors' muscle memory; a shim costs nothing and `git mv` preserves
history. The shim:

```bash
#!/usr/bin/env bash
# Deprecated: renamed to check-gates.sh (gates 1-4, not just lint). Kept for compatibility.
exec "$(dirname "$0")/check-gates.sh" "$@"
```

Document both in `scripts/README.md` under a new `## Verification gates` section — that is the
natural home per the last discretion bullet, and `scripts/README.md` currently documents only
the three `npm run` extraction commands, so a gates section is additive.

---

## Issue script (INFRA-02, D-01 … D-05, D-09)

### Environment facts

| Fact | Value | Verified by |
|------|-------|-------------|
| Repo slug | `Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify` | `git remote -v` |
| `gh` version | 2.100.0 | `gh --version` |
| `gh` authenticated? | **yes** — account `astefano`, keyring token, scopes `gist, read:org, repo, workflow` | `gh auth status` |
| Open issues today | 53 | `gh issue list --state open --limit 500 --json number --jq length` |
| Umbrella issue | #44 `Prove chain and state machine invariants (PROP-9,14,17,21,26,30,33,39)`, OPEN, labels `Proof`, `Specification` | `gh issue view 44` |
| Per-function issues | #510–#533 (plus #412–#523 range), titled `Specify and verify \`spqr::…\` in \`file.rs\``, **no labels** | `gh issue list` |
| PR body shape | #541: title `Specify and verify \`spqr::chain::{spqr::chain::Chain}::add_epoch\` in \`chain.rs\``; body = one sentence + `closes #513` | `gh pr view 541` |

The `repo` scope is sufficient for both `gh label create` and `gh issue create`.

### Labels: the template's scheme does not exist in the repo

`gh label list` returns **six** labels, none of them `type:*` or `status:*`:

```
Documentation  Improvements or additions to documentation  #0075ca
Infrastructure                                             #31e4e6
Proof                                                      #d93f0b
Specification                                              #2c14d4
Sorry          Issue tracking a `sorry` expression …       #b60205
protocols-bridging                                         #a472ed
```

[VERIFIED: `gh label list --limit 100`]

So the idempotent label step will **create all of them** on first run. The label set implied by
`docs/ISSUE_TEMPLATE.md` (its "Labels" HTML comment, L112–125) is:

- Type (pick one): `type:algebraic-spec`, `type:state-invariant`, `type:behavioral-spec`,
  `type:correspondence`, `type:serialization`, `type:deviation-flag`, `type:history-erasure`,
  `type:progress`, `type:proof-infra` — **9**
- Status (pick one): `status:open`, `status:axiom`, `status:proved-branch`, `status:proved`
  — **4**
- Special: `modelling-assumption`, `spec-deviation` — **2**

**15 labels total.** Note the divergence D-03 refers to: `issues/create_issues.sh:56-63` uses
`status:provable-now`, `status:feasible`, `status:axiom-required`, `status:blocked`,
`status:proved` and a `tier:1..4`/`tier:proved` axis. **None of those are the template's
scheme**; do not create them. Reuse the old script's *colors* for the 9 `type:*` labels and the
2 special labels (they are already chosen and reasonable); pick four for the status axis, e.g.
`status:open`=`d93f0b`, `status:axiom`=`fbca04`, `status:proved-branch`=`bfd4f2`,
`status:proved`=`2ea44f`, mapping to catalog §-header status values one-to-one as D-03 requires.

### Idempotency: the exact `gh` invocations

**Labels** — `gh label create` with `--force` *updates* an existing label's color and
description instead of failing (`gh label create --help`: "Create a new label on GitHub, or
update an existing one with `--force`"). That is the idempotent form:

```bash
gh label create "$name" --color "$color" --description "$desc" --force --repo "$REPO"
```

Without `--force`, a duplicate returns a non-zero exit and prints `already exists`. Do not
paper over it with `|| true` (the old script's approach, `create_issues.sh:67-70`) — that also
swallows auth and network errors. [VERIFIED: `gh label create --help`]

**Issues** — `gh issue create` has **no** `--dry-run`. Dry-run must be implemented in the
script (print the title, labels, and body path; do not call `gh`). D-01 requires the user to
review a dry-run listing first, so dry-run is the default and `--execute` opts in — same shape
as the old script (`create_issues.sh:18-21`).

**Detecting an already-filed issue** — GitHub's search indexes both titles and bodies.
Verified in this session:

```
$ gh issue list --state all --search "add_epoch in:title" --json number,title --limit 5
[{"number":513,"title":"Specify and verify `spqr::chain::…::add_epoch` in `chain.rs`"}]

$ gh issue list --state all --search "\"closes #513\"" --json number --limit 3
[{"number":513}]
```

Recommend **exact-title matching**, not body-marker matching: body search is
full-text and fuzzy; an HTML-comment marker may or may not be indexed; titles here are
deterministic (`PROP-42: KDF_AUTH info and length`). Pattern:

```bash
existing="$(gh issue list --repo "$REPO" --state all --limit 200 \
  --search "\"$title\" in:title" --json number,title \
  --jq --arg t "$title" '.[] | select(.title == $t) | .number' | head -1)"
if [[ -n "$existing" ]]; then
  echo "SKIP  $id → already filed as #$existing"
else
  num="$(gh issue create --repo "$REPO" --title "$title" \
          --label "$type_label,$status_label" --body-file "$body_file")"
fi
```

`--jq` with `--arg` gives an exact string comparison, defeating search's substring behaviour.
`gh issue create` prints the new issue's URL on stdout — parse the trailing number for the
"report the issue number so the user opens the PR with `Closes #N`" step of D-09.

**Use `--body-file`, not `--body "$(cat <<'EOF' …)"`.** The old script builds a shell string
and `eval`s it (`create_issues.sh:28-34, 79-88`). With property text containing backticks,
`$`, quotes and Lean's `⦃ ⦄`, `eval` is both a correctness hazard and an injection hazard.
Write the body to a temp file and pass `--body-file`. See §Security Domain.

### Template field set and how a generated body is filled

`docs/ISSUE_TEMPLATE.md` (127 lines) is a Markdown document with `{PLACEHOLDER}` tokens and
HTML-comment guidance. The fillable fields, in document order:

| Placeholder | Line | Source for a generated body |
|---|---|---|
| `{PROP-ID}` | 10 | the catalog row ID (`PROP-42`, `LEAN-ENC-2`) or requirement ID (`INFRA-01`) |
| `{TYPE}` | 14 | one of the 9 prose types listed in the comment L16-26 |
| `{SOURCES}` | 28 | comma-separated tags from L30-40 (`production-code`, `spec-mlkembraid §2.5`, …) |
| `{DESCRIPTION}` | 46 | the catalog section paragraph for the property |
| `{LEAN_STATEMENT}` | 58 | the WP-style statement, or "TBD — written in this PR" |
| `{DIFFICULTY}` | 68 | Easy / Medium / Hard / Axiom-only |
| `{STATUS}` | 71 | **must be a catalog status value**: Proved / Proved (branch) / Open / Axiom (comment L72-73) |
| `{APPROACH}` | 75 | short proof-strategy line |
| `{DEPENDENCIES}` | 83 | prerequisite property IDs, axioms, blockers, or "None" |
| `{TYPE_LABEL}`, `{STATUS_LABEL}` | 127 | the two labels, mirroring `{TYPE}` and `{STATUS}` |

The Checklist block is **L93-98** and currently reads:

```
- [ ] Lean theorem statement written
- [ ] Proof completed
- [ ] PHANTOM-TOKEN passes            ← L98, the line INFRA-01 replaces
- [ ] Status updated in `docs/spqr-properties.md`
```

**Recommended replacement** (satisfies INFRA-01's "four gates by command" and CAT-01's
"catalog-and-index update line"):

```markdown
### Checklist

- [ ] Lean theorem statement written
- [ ] Proof completed
- [ ] `lake build` clean — no warning other than `declaration uses 'sorry'`
- [ ] `lake exe runLinter Spqr` clean — no `error:` line
- [ ] `lake env lean scripts/Audit.lean` — `sorry-manifest.txt` gains no `Spqr.Specs.*` line
- [ ] `#print axioms <theorem>` — only `propext`, `Classical.choice`, `Quot.sound` and the
      documented stubs of `docs/spqr-properties.md` §1
- [ ] Module re-exported from `Spqr.lean` (otherwise `scripts/Audit.lean` cannot see it)
- [ ] `docs/spqr-properties.md` updated in the same PR: the property's **status row**, its
      **section text**, and the **§12 index** entry (CAT-01)

All four gates in one command: `./scripts/check-gates.sh <theorem-name>`
```

The `Spqr.lean` re-export line is not required by INFRA-01, but it is the failure mode
`Audit.lean`'s own header warns about and the one `spqr-eval` explicitly hunts ("a module that
is not imported is invisible to `scripts/Audit.lean`"). Adding it costs one line and removes a
whole class of false-green.

### Layout recommendation (Claude's discretion)

**Bash with a data table, not a catalog parser.** Concretely:
`scripts/create-property-issues.sh` + `scripts/property-issues.tsv`.

- `property-issues.tsv`: one row per deliverable, tab-separated —
  `id`, `title`, `type`, `sources`, `difficulty`, `status`, `type_label`, `status_label`,
  `dependencies`, `related` (space-separated issue numbers), `description_anchor`
  (the catalog heading to quote, e.g. `### PROP-42 KDF_AUTH info and length`).
- The script renders `docs/ISSUE_TEMPLATE.md` by substituting placeholders, pulling
  `{DESCRIPTION}` from the catalog section named by `description_anchor` (a `sed -n` range
  between that heading and the next `### `). This keeps D-05's "one source of truth" honest for
  both the body *shape* (template) and the property *text* (catalog).
- Usage: `./scripts/create-property-issues.sh [--execute] [--repo SLUG] [ID ...]`.
  With no IDs it processes all rows (the batch listing D-01 wants the user to review). With
  IDs it files exactly those — which is what D-09's just-in-time filing needs.

Why not a full catalog parser: the catalog's section text is prose, and the type/difficulty/
dependency fields are editorial judgements with no machine-readable home. A TSV makes those
judgements reviewable in the PR diff. Why not per-issue heredocs (the old script's shape):
2203 lines of duplicated body text is precisely the "one source of truth" failure D-05
rejects.

### Cross-linking (D-02)

Each body gets a trailing block:

```markdown
### Related

Umbrella: #44. Overlapping per-function issues: #519, #522.
This issue does not supersede them; it tracks the catalog row PROP-37.
```

The mapping from a catalog property to the overlapping `#510–#533` issues must be written by
hand into the TSV `related` column — there is no mechanical link (the per-function issues are
titled by Rust path, the catalog rows by property ID). Budget a task for it. #44 explicitly
covers PROP-9, 14, 17, 21, 26, 30, 33, 39.

### What gets deleted under `issues/`

All three entries: `issues/create_issues.sh` (2203 lines), `issues/SPQR_ISSUES_PREVIEW.md`
(2119 lines), `issues/272/README.md` (101 lines) — i.e. the whole `issues/` directory. Per
B-1 this is a filesystem-only action; the reviewable hunk is the `.gitignore:25` removal.
`issues/272/README.md` documents a real finding (#272's diagnosis is wrong; the fix is on
`fix/272-frame-condition-loop0-body-spec`) whose `.lean` evidence files are already gone. If
that analysis is worth keeping, it belongs in the #272 GitHub issue thread, not in an ignored
directory — flag it to the user at the PR A boundary rather than deleting silently.

---

## PHANTOM-TOKEN inventory (INFRA-01, D-17)

Exhaustive, from `grep -rn <phantom> . --exclude-dir=.git --exclude-dir=.lake
--exclude-dir=node_modules`:

| # | File:line | Current context | D-17 action |
|---|-----------|-----------------|-------------|
| 1 | `docs/ISSUE_TEMPLATE.md:98` | `- [ ] \`<phantom>\` passes` | replace with the four-gate checklist above |
| 2 | `docs/rubrics/spqr-plan-review.md:110` | "…and the documented stubs. `<phantom>` does not exist in this repository; a plan citing it has a broken gate." | reword to "a plan citing a gate that does not exist in the repository has a broken gate" |
| 3 | `CLAUDE.md:24` | Constraints → Gates bullet: "`#<phantom>` in `docs/ISSUE_TEMPLATE.md` does not exist in the repo; the real checks are …" | reword: drop the token, keep "the real gates are …", and update "The template should be corrected in the first phase" → past tense / point at `scripts/check-gates.sh` |
| 4 | `.planning/PROJECT.md:67` | identical sentence to #3 | **not in D-17** |
| 5 | `.planning/STATE.md:66` | "Real gates are …; `#<phantom>` does not exist and is corrected in Phase 1" | **not in D-17** |
| 6 | `.planning/REQUIREMENTS.md:15` | INFRA-01's own text | **not in D-17** |
| 7 | `.planning/ROADMAP.md:56` | Phase 1 success criterion 1 | **not in D-17** |
| 8 | `.planning/phases/01-…/01-CONTEXT.md:105,114,118,147,149` | five hits in D-15, D-17 and canonical refs | **not in D-17** |
| 9 | `.planning/phases/01-…/01-DISCUSSION-LOG.md:159` | section heading | **not in D-17** |

All nine files are tracked. See Open Question Q-1.

Note the self-reference trap: #6 and #7 are the requirement and criterion **that mandate the
removal**. Rewording them is not optional if the unscoped grep is kept — INFRA-01 would have
to become "…instead of a gate that does not exist in the repository", and criterion 1 would
have to stop naming the token it is testing for.

---

## Catalog surgery (DEV-01..04, CAT-01)

All line numbers are in `docs/spqr-properties.md` (518 lines) at `la/spec-catalog` `f44568b`.

### §11 current shape (L430–L447)

Heading `## 11. Deviations from the spec` at **L430**. One table, **five columns**:

```
| ID | Where | Spec | Code | Impact |
|----|-------|------|------|--------|
```

followed by a five-row body (D1–D5, one line each) and a closing paragraph at **L443–447**:

> Resolution for each is a decision, not a proof: D1 needs either a code fix or a spec
> erratum; D2 needs the spec to mandate strictness or the code to adopt the no-op; D3 and D4
> need the spec to document the extra message handling or the code to drop it; D5 needs the
> caller's contract written down. Until decided, the properties above describe the code as it
> is.

Per the CONTEXT §Specific Ideas, that last sentence becomes the **definition of
`Status = Provisional`**.

D-12 adds two columns → **seven**: `| ID | Where | Spec | Code | Impact | Decision | Status |`.
Seven columns of long prose makes an unreadable line; this is a real formatting problem the
planner should decide up front. Two viable shapes:

- **(a) Widen the existing table.** Mechanically simplest, honours "keeps its single table"
  literally. Lines become ~600 chars.
- **(b) Keep the five-column table and add a second, narrow decision table** directly beneath:
  `| ID | Decision | Status |` with three short columns. Still "no per-deviation subsections"
  (D-12's actual prohibition), far more readable, and it is the table Phase 5/6 plans will
  actually quote.

**Recommend (b)**, and say so explicitly in the plan so the reviewer does not read it as
drifting from D-12. If the user prefers (a), it is a one-task change.

The five rows, **verbatim**, are the text DEV-01..04 must extend:

- **D1** | `Authenticator::update` (`authenticator.rs:43-54`) | KDF_AUTH: salt = `root_key`,
  IKM = `update_key` | salt = `[0u8; 32]`, IKM = `root_key ‖ update_key` | *Different key
  bytes. Not a weakness, but a spec-conformant peer cannot interoperate. Needs a decision from
  Signal on which side is authoritative.*
- **D2** | every `recv` arm | `msg.epoch > epoch` ignored | `Err(EpochOutOfRange)` (except
  Ct2Sampled at `epoch + 1`) | *Tightening; a future-epoch message is an error instead of a
  no-op.*
- **D3** | `EkSentCt1Received.send` (`states.rs:182`), `EkReceivedCt1Sampled.recv`
  (`states.rs:464-467`) | sends `None`; accepts only `EkCt1Ack` | sends `Ct1Ack(true)`;
  accepts `Ct1Ack(true)` too | *§2.3 defines the `Ct1Ack` type but §2.5 never uses it; the code
  does. `Ct1Ack(false)` is never emitted. Motivation is robustness to a lost acknowledgement;
  no reachable state pair of the spec machine deadlocks without it.*
- **D4** | `Ct1Acknowledged.recv` (`states.rs:484-492`) | accepts `EkCt1Ack` | also accepts
  `Ek` chunks | *Out-of-order delivery; comment at `states.rs:485-488`. Integrity still checked
  by PROP-25.*
- **D5** | MAC failure (§2.4) | "should not proceed with the session and should negotiate a new
  session" | returns `Err`; caller keeps the previous state and may retry | *Weaker than the
  spec; the session is not aborted by the library.*

Per D-10 every `Decision` cell is "code as implemented is authoritative" and every `Status`
cell is `Provisional (2026-09-14)`.

### The five property statements DEV-01..04 must touch

| Property | Heading line | Current closing sentence / status | What must change |
|---|---|---|---|
| **PROP-42** (§5) | L204 | "Info and length match §2.2. Salt and IKM do not: see deviation D1. **Proved** as `update_spec` (`Spqr/Specs/Authenticator/Authenticator/Update.lean`)." | D-14: align with the D1 provisional decision — say the *code's* salt/IKM is the stated behaviour and that `update_spec` proves it, with D1 marked Provisional |
| **PROP-43** (§7) | L285 | "…`States::recv` returns `Err`, and `lib.rs` writes no new state (it re-decodes state from bytes and stores only on `Ok`, `lib.rs:356-425`). In transition 5 the check runs after `decaps` and after `auth.update`, matching the spec's order. Status: **Open**. See deviation D5 for the spec's stronger requirement." | D-13: add the written caller contract here; §11 D5 points at it |
| **PROP-30** (§8) | L305 | 6-row dispatch table; rows 4 and 6 say `Err(EpochOutOfRange)` / "no-op (D2)". Status line: "Less and Greater rows **Proved (branch)** (`Recv.lean`, one theorem per variant); Equal rows **Open**." | D-14: state the provisional D2 behaviour (strict `Err`) as the one to be proved, citing D2 |
| **PROP-47** (§8) | L321 | 13-row transition table; row 11 "also accepts Ek (D4)", row 12 "also accepts Ct1Ack(true) (D3)"; trailing paragraph "…except `EkSentCt1Received.send`, which emits `Ct1Ack(true)` where the spec emits `None` (D3)." Status **Open** for all 13. | D-14: make D3/D4 acceptance the provisionally-decided behaviour the Phase 5 theorems prove |
| **PROP-50** (§8) | L349 | "…D2 matters here: a future-epoch message is an error rather than a no-op, so the property holds only for in-order delivery across epochs. Status: **Open**." | D-14: restate for the D2 provisional decision so Phase 6's TRACE-04 quotes it verbatim |

### §12 index (L449–L491) — CAT-01's target

Heading `## 12. Index` at **L449**. Three columns:

```
| ID | Section | Status |
|----|---------|--------|
| PROP-1 | 2 | Open (needs PROP-3 axiom) |
| PROP-42 | 5 | Proved |
| …
| D1–D5 | 11 | Deviations |
```

38 rows. `Section` is a bare section *number*, not a link. `Status` is the catalog status value,
optionally qualified in parentheses (`Proved (branch), Less/Greater rows; Equal rows Open`).
The last row is `| D1–D5 | 11 | Deviations |`.

CAT-01 needs the template checklist to name this table explicitly, which the recommended
checklist line above does ("**§12 index** entry"). No §12 row changes in Phase 1 (no status
changes); if the planner prefers, the D1–D5 row's `Status` cell could become
`Deviations (D1–D5 provisional)` — cosmetic, and it makes PR B's §12 touch non-empty, which is
a nice demonstration of CAT-01's rule in the very PR that introduces it. Recommend doing it.

### D5 caller contract — the `src/` evidence (read-only; `src/` is frozen)

Three lines establish the contract; quote these `path:line` refs in the §7 text so the Phase 5
AUTH-01 theorem and the plan reviewer can both re-verify them:

| Fact | Evidence |
|---|---|
| A failed header MAC returns `Err(InvalidHdrMac)`, propagated by `?` out of `recv_header` before `HeaderReceived` is constructed | `src/v1/unchunked/send_ct.rs:107` (`self.auth.verify_hdr(self.epoch, &hdr, mac)?;`); the error value at `src/authenticator.rs:84` (`Err(Error::InvalidHdrMac)`), raised from `verify_hdr` at `src/authenticator.rs:82` |
| A failed ciphertext MAC returns `Err(InvalidCtMac)`, propagated by `?` **after** `decaps`, the KDF_OK derivation and `auth.update` | `src/v1/unchunked/send_ek.rs:160` (`auth.verify_ct(epoch, &ct1, &mac)?;`), preceded by `decaps` at :150, `hkdf_to_vec` at :156 and `auth.update(epoch, &ss)` at :158; error value at `src/authenticator.rs:59` |
| The library takes state **by reference** and only ever returns a *new* serialized state inside `Ok`; on any `Err` the caller's `SerializedState` is untouched and the library performs no abort, no zeroization and no session teardown | `src/lib.rs:356` `pub fn recv(state: &SerializedState, msg: &SerializedMessage) -> Result<Recv, Error>`; the MAC error propagates at `src/lib.rs:425` (`…States::from_pb(pb)?.recv(&scka_msg)?`); the only state write is the `Ok(Recv { state: …encode_to_vec(), … })` at `src/lib.rs:437-451` |

So the contract to write under PROP-43 is exactly: **`spqr::recv` returns
`Err(Error::MacVerifyFailed)`; it mutates nothing; the caller's previous `SerializedState` remains
valid and may be reused for a retry; the library does not terminate the session — deciding
whether to negotiate a new session on repeated MAC failure is the caller's responsibility.**

> **Correction (plan review 01, 2026-09-14).** An earlier draft of this paragraph said
> `spqr::recv` returns `Err(InvalidHdrMac)` / `Err(InvalidCtMac)`. That is wrong at the
> public boundary. `InvalidHdrMac` and `InvalidCtMac` are variants of
> **`authenticator::Error`** (`src/authenticator.rs:13,15`), and
> `impl From<authenticator::Error> for Error` (`src/lib.rs:145-149`) maps *every*
> authenticator error to the single public variant `Error::MacVerifyFailed`
> (`src/lib.rs:106`). `spqr::Error` has no `InvalidHdrMac`/`InvalidCtMac` variant at all.
> The two internal causes are therefore **indistinguishable to a caller**, and the D5
> caller contract must say so. The internal error values remain correctly cited in the
> rows above — they are what `verify_hdr`/`verify_ct` raise, which is the level PROP-15
> speaks at (`docs/spqr-properties.md:282`). [VERIFIED: `src/lib.rs:145-149`,
> `src/authenticator.rs:11-23`, `src/lib.rs:98-128`, `SrcTranslated/Types.lean:795-799`]
Note the asymmetry worth stating: on a `verify_ct` failure the *epoch secret has already been
derived and `auth.update` has already run on the local `auth` copy*, but because `recv_ct2`
consumed `self` and returns `Err`, that updated authenticator is dropped — the caller's stored
state still holds the pre-`update` authenticator. That is the non-obvious half of the contract
and the one Phase 5's theorem must capture.

### `docs/signal-deviation-questions.md` (D-11)

Kebab-case ✓ (PC-8). Five sections, one per deviation, each carrying: the spec text (§2.2 for
D1, §2.5 for D2/D3/D4, §2.4 for D5), the `src/` lines from the §11 `Where` column, the impact
sentence from the §11 `Impact` column, and the two candidate resolutions already named in the
§11 closing paragraph (code fix vs spec erratum for D1; mandate strictness vs adopt the no-op
for D2; document the extra handling vs drop it for D3/D4; write the caller contract for D5).
Close each with "Absent a ruling, we are proceeding with: *the code as implemented is
authoritative* (recorded as Provisional in `docs/spqr-properties.md` §11)."

---

## Review gates

Both gates are mandatory per CLAUDE.md and the ROADMAP process paragraph.

**Before execution — `/spqr-plan-review 1`.** Codex CLI is installed (`codex-cli 0.145.0`);
the skill's preflight requires `codex login status` to succeed or an `env_key` from
`~/.codex/config.toml` to be set — the SKILL notes the API key lives in `~/.secrets/openrouter`
and must be `source`d first. Output persists as `01-CODEX-REVIEW.md` (append-only: `-2`, `-3`
if re-run). Only APPROVE, or APPROVE-WITH-EDITS with every edit triaged and applied, routes to
execution.

**Rubric item 7 is about this phase's subject matter.** Write the plans to pass it:
- Every verification command in every task must be **runnable as written**. The reviewer's
  sandbox is read-only and cannot run `lake build` — it judges by reading. So quote exact
  commands, exact file paths, and exact expected output strings.
- The rubric itself currently names the PHANTOM-TOKEN at `spqr-plan-review.md:110`. PR A
  rewords it. Sequence the plan so the rubric edit happens *in* PR A, and be aware the
  pre-execution review runs against the **pre-edit** rubric — the reviewer will read its own
  rubric mentioning a token the plan proposes to delete. Say so in the plan's context so it is
  not filed as a finding.
- Rubric item 8 (boundedness / code freeze): every plan must state `src/` and `SrcTranslated/`
  are untouched, and `allowed_sorries: 0` — even though no Lean lands, the field's absence is
  itself reviewable.
- Rubric item 9 (roadmap coherence): the ROADMAP criterion-3 rewording (D-09) and the
  criterion-1 scoping (Q-1) must be *in a task*, not assumed. A plan whose endpoint does not
  match the ROADMAP's stated criteria is a MAJOR finding.

**After execution — `spqr-eval`** on the phase diff, alongside `gsd-verifier`, persisted as
`01-EVAL.md`. FOLLOWUP routes to a gap-closure plan; HUMAN_RULING stops for the user. Note
`spqr-eval` is tuned for Lean theorem diffs ("Statement fidelity", "Arm coverage", "Concrete
traces") — for a docs-and-scripts phase it will mostly exercise its "Catalog sync" and
"Trusted base" lenses. Its instruction that *any hunk under `src/` or `SrcTranslated/` is
itself a finding* applies with full force here.

---

## Don't Hand-Roll

| Problem | Don't build | Use instead | Why |
|---|---|---|---|
| Manifest delta computation | a `comm`/`diff`/`awk` comparison in bash | `python3 scripts/sorry-diff.py base head` with `SORRY_FAIL_ON_NEW=true` | It already keys on the declaration column only, already filters to `Spqr.Specs.*`, already handles a missing baseline, and is *the same code CI runs*. A bash reimplementation is guaranteed to drift from CI, which is exactly what criterion 2 forbids. |
| Axiom closure computation | a Lean script that walks `getUsedConstants` | `#print axioms` (gate 4) and `scripts/Audit.lean` (gate 3) | `Audit.lean` already caches `Lean.collectAxioms` for every project declaration; D-08 explicitly says don't change it. |
| Building `main` to get a baseline | copying `.lake` between trees, or symlinking build dirs | `git worktree` + `lake exe cache get` | Lake's build is path-sensitive; a shared `.lake` across two source trees produces silently stale oleans. |
| Mathlib oleans | `lake build` from source | `lake exe cache get` | Hours vs minutes. Mathlib is transitive via aeneas. |
| Idempotent label creation | `gh label create … \|\| true` | `gh label create … --force` | `\|\| true` also swallows auth failures, rate limits and typos — the script reports success having created nothing. |
| Issue-body interpolation | shell string building + `eval` (the old script's approach) | write to a temp file, `gh issue create --body-file` | Property text contains backticks, `$`, `‖`, `⦃ ⦄` and quotes. `eval` on that is a correctness and injection hazard. |
| Duplicate-issue detection | keeping a local "already filed" state file | `gh issue list --state all --search "\"$title\" in:title"` + exact `--jq` match | The GitHub API is the state; a local file drifts the moment anyone files an issue in the browser. |
| Deciding whether a run matched CI | eyeballing two logs | run the same commands with the same log paths and the same greps, and diff the script's output against the CI job log | Criterion 2 is literally "its result on `main` matches CI's". |

**Key insight:** every gate in this repository already has exactly one implementation. The
value this phase adds is a *runner* that invokes all four in the right order with the right
baseline — not a second implementation of any of them. A plan task that rewrites
`sorry-diff.py`'s logic in bash should be rejected.

---

## Common Pitfalls

### P-1 — The gate script passes because the theorem name was misspelled
**What goes wrong:** `#print axioms Spqr.Specs.Foo.bar_spce` elaborates to
`unknown identifier`, the allowlist grep finds no forbidden axiom, the script prints PASS.
**Why:** greping *for* bad names instead of *validating* that each target produced a
well-formed report.
**How to avoid:** assert one `'<name>' depends on axioms:` or
`'<name>' does not depend on any axioms` line **per requested target**; count them; fail if
the count is short or any `unknown` appears.
**Warning sign:** the script passes on a name you invented.

### P-2 — Gate 1 passes because the build was a no-op
**What goes wrong:** `lake build` on an already-built tree emits no warnings at all, so the
`grep -v` finds nothing and gate 1 "passes" without having recompiled the changed module.
**Why:** warning text lives in the compilation output, not in a persisted report.
**How to avoid:** this is CI's behaviour too (fresh checkout, always a full build), so the
local script inherits the gap. Document it in `scripts/README.md`; offer `--clean` for a
pre-PR confirmation run. Do not make `--clean` the default — it is a multi-hour operation.

### P-3 — The baseline worktree silently drifts from the pinned toolchain
**What goes wrong:** the worktree checks out a `main` whose `lean-toolchain` or aeneas `rev`
differs from the working branch; the two manifests then differ for toolchain reasons and every
run reports a phantom delta.
**Why:** `elan` picks the toolchain per directory from `lean-toolchain`.
**How to avoid:** the script should compare `lean-toolchain` and the aeneas `rev` in
`lakefile.toml` between the two trees and **warn loudly** when they differ, since PC-3 says a
toolchain bump is separate work. Today they are identical
(`leanprover/lean4:v4.31.0`, `nightly-2026.08.27-5b9dcf3`) and there are zero Lean diffs vs
`origin/main`.

### P-4 — `sorry-manifest.txt` in the working tree is mistaken for a baseline
**What goes wrong:** the checked-out file is dated 2026-08-07 and gitignored; using it as
`base` makes the delta meaningless.
**How to avoid:** always regenerate the head manifest in this run and always source the base
from the SHA-keyed cache. Never read the repo-root file as a base.

### P-5 — The issue script files duplicates on a re-run
**What goes wrong:** D-09's just-in-time filing means the script is run many times over the
milestone's life; without exact-title detection, PR B's run re-files PR A's issues.
**How to avoid:** the exact-title `--jq` match above, plus a dry-run default, plus a printed
`SKIP  <id> → already filed as #N` line so the skip is visible.

### P-6 — The catalog and the theorem drift because the catalog edit is a separate PR
**What goes wrong:** PC-5 requires the catalog change in the *same* PR as the statement. PR B
changes wording for theorems that do not exist yet (phases 5–6).
**Why it is still right:** DEV-01..04 are *decisions*, not theorem statements — recording them
early is the whole point of Phase 1 (the roadmap's "so no later theorem has to be restated").
**How to avoid a finding:** say this explicitly in the plan and in PR B's body. Otherwise the
reviewer reads it as a PC-5 violation.

### P-7 — Committing this phase's own artifacts re-introduces the PHANTOM-TOKEN
**What goes wrong:** criterion 1's grep is repo-wide; a plan, summary or eval file that quotes
the token fails it.
**How to avoid:** Q-1's scoped grep, plus the notation convention at the top of this document
applied to every Phase 1 artifact.

### P-8 — `gh issue create` output is not the issue number
**What goes wrong:** it prints a URL
(`https://github.com/…/issues/1234`), not a bare number; naive capture puts a URL into
`Closes #N`.
**How to avoid:** `num="${url##*/}"`.

---

## Code Examples

### Gate runner skeleton (`scripts/check-gates.sh`)

```bash
#!/usr/bin/env bash
# Runs the four repository gates locally, mirroring .github/workflows/lean.yml.
#   ./scripts/check-gates.sh [--no-delta] [--refresh-baseline] [--clean] [THEOREM ...]
set -euo pipefail
export LEAN_ABORT_ON_PANIC=1          # matches lean.yml env block
REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"
fail=0

# --- Gate 1: build warnings (byte-for-byte with lean.yml "Build and check…") ---
echo "=== Gate 1: build warning check ==="
lake build --no-ansi 2>&1 | tee /tmp/lake-build.log
if grep 'warning:' /tmp/lake-build.log | grep -qv 'declaration uses .sorry'; then
  echo "FAIL: non-sorry warnings found:"
  grep 'warning:' /tmp/lake-build.log | grep -v 'declaration uses .sorry'
  fail=1
else echo "PASS"; fi

# --- Gate 2: lint (byte-for-byte with lean.yml "Lint hand-written code") ---
echo "=== Gate 2: lint check ==="
lake exe runLinter Spqr 2>&1 | tee /tmp/lake-lint.log || true
if grep -q 'error:' /tmp/lake-lint.log; then
  echo "FAIL: lint errors in hand-written code:"; grep 'error:' /tmp/lake-lint.log; fail=1
else echo "PASS"; fi

# --- Gate 3a: axiom audit + manifest regeneration ---
echo "=== Gate 3a: axiom audit (scripts/Audit.lean) ==="
lake env lean scripts/Audit.lean 2>&1 | tee /tmp/lake-audit.log
test -f sorry-manifest.txt || { echo "FAIL: no sorry-manifest.txt produced"; fail=1; }

# --- Gate 3b: manifest delta vs origin/main (see worktree recipe above) ---
# ... baseline block ...
if [[ -f "$BASE_MANIFEST" ]]; then
  echo "=== Gate 3b: sorry delta vs $BASELINE_REF ==="
  SORRY_FAIL_ON_NEW=true python3 scripts/sorry-diff.py \
      "$BASE_MANIFEST" sorry-manifest.txt || fail=1
  rm -f .sorry-delta-comment.md
else
  echo "=== Gate 3b: SKIPPED (no baseline; run with --refresh-baseline) ==="
fi

# --- Gate 4: per-theorem trusted base ---
# ... scratch-file block, allowlist from scripts/axiom-allowlist.txt,
#     one report line asserted per requested theorem ...

exit $fail
```

Note the accumulator `fail=1` rather than `exit 1` per gate: a local runner should report **all**
failing gates in one pass. CI exits at the first failure because each gate is a separate step;
that difference does not affect criterion 2, which is about the pass/fail *verdict*.

### Idempotent label creation

```bash
while IFS=$'\t' read -r name color desc; do
  [[ "$name" == \#* || -z "$name" ]] && continue
  if $DRY_RUN; then
    echo "[DRY-RUN] gh label create $name --color $color"
  else
    gh label create "$name" --color "$color" --description "$desc" --force --repo "$REPO"
  fi
done < scripts/property-issue-labels.tsv
```

### Issue filing with exact-title idempotency

```bash
file_issue() {                       # $1=id  $2=title  $3=labels  $4=body_file
  local existing
  existing="$(gh issue list --repo "$REPO" --state all --limit 200 \
      --search "\"$2\" in:title" --json number,title \
      --jq --arg t "$2" 'map(select(.title == $t)) | .[0].number // empty')"
  if [[ -n "$existing" ]]; then
    echo "SKIP  $1 → already filed as #$existing"; return 0
  fi
  if $DRY_RUN; then
    echo "[DRY-RUN] $1  labels=$3"; echo "          title: $2"; return 0
  fi
  local url; url="$(gh issue create --repo "$REPO" --title "$2" \
                      --label "$3" --body-file "$4")"
  echo "FILED $1 → #${url##*/}"
}
```

---

## Runtime State Inventory

This phase renames a token, retires a directory and creates GitHub state. The question "after
every file in the repo is updated, what runtime systems still hold the old string, or hold new
state that git does not?" has real answers here.

| Category | Items found | Action required |
|----------|-------------|------------------|
| **Stored data** | **GitHub issues are the store.** 53 open issues. #44 (umbrella, labels `Proof`+`Specification`) and #510–#533 / #412–#523 (per-function, **no labels**) overlap the new per-property issues. D-02 forbids editing them. New issues created by this phase live only on GitHub — no git artifact records their numbers. | Cross-link only. **Add a task** to record filed issue numbers back into the phase SUMMARY (and, per D-09, into the PR-boundary report), otherwise the numbers exist nowhere the next phase can read them. |
| **Live service config** | **GitHub labels.** 15 labels must be created; they live in GitHub, not in git. Also GitHub Actions **caches**: `sorry-manifest-main-<sha>` keys written by pushes to `main` (`lean.yml:80-84`) — unaffected by this phase but they are the CI-side twin of the local baseline cache. | Idempotent `gh label create --force` step, re-runnable. No cache action. |
| **OS-registered state** | **None.** No cron, systemd unit, pm2 process, Task Scheduler entry or launchd plist references anything this phase touches — verified by the absence of any such config in the repo and by the fact that all tooling is invoked manually or by GitHub Actions. | None. |
| **Secrets / env vars** | `gh` token in the system keyring (scopes `gist, read:org, repo, workflow`) — used, not changed. `CODEX_HOME`/`~/.secrets/openrouter` for the plan-review gate — used, not changed. New **script-level** env vars introduced by this phase: `SPQR_BASELINE_REF`, `SPQR_BASELINE_WORKTREE`, `SPQR_GATE_CACHE`, plus `SORRY_FAIL_ON_NEW` (existing, consumed). | Document the four in `scripts/README.md`. No secret changes. |
| **Build artifacts** | `sorry-manifest.txt` at repo root is **stale** (2026-08-07) and gitignored. `.lake/build` does **not exist** — the tree is unbuilt. A new `.gate-cache/` and a sibling `spqr-gate-baseline` worktree with its own multi-GB `.lake` will be created. An existing unrelated worktree lives at `/home/lacra/git_repos/baif/spqr-pr340`. | Regenerate (never read) the manifest. `.gitignore`: **add** `.gate-cache/` and `.sorry-delta-comment.md`; **remove** `issues/`. Document how to tear down the baseline worktree (`git worktree remove`). |

**The canonical answer:** after PR A and PR B land, the residual non-git state is (1) the 15
GitHub labels, (2) the filed issues and their numbers, (3) the local `.gate-cache/` and the
baseline worktree. Only (1) and (3) are reproducible from the repo; (2) must be written down.

---

## Environment Availability

| Dependency | Required by | Available | Version | Fallback |
|------------|------------|-----------|---------|----------|
| `git` | everything, worktree baseline | ✓ | 2.55.0 | — |
| `bash` | gate + issue scripts | ✓ | system | — |
| `python3` | `scripts/sorry-diff.py` | ✓ | 3.12.3 | — |
| `gh` | labels, issues | ✓ authenticated as `astefano`, scopes include `repo` | 2.100.0 | none — issue filing is blocked without it |
| `jq` | `gh --jq` is built in; standalone `jq` for TSV work | ✓ | 1.7 | `gh --jq` alone suffices |
| `lake` / `lean` | gates 1–4 | ✓ | Lake 5.0.0-src, Lean 4.31.0 (matches `lean-toolchain`) | — |
| `elan` | toolchain pinning in the worktree | ✓ | present at `~/.elan/bin` | — |
| `lake exe cache get` (mathlib) | worktree baseline build | ✓ target exists (`mathlib/lakefile.lean:101`) | — | build mathlib from source (hours) |
| `lake exe runLinter` (batteries) | gate 2 | ✓ target exists (`batteries/lakefile.toml:22`) | — | — |
| `codex` | `/spqr-plan-review 1` | ✓ binary present | codex-cli 0.145.0 | auth unverified — SKILL preflight must run; key at `~/.secrets/openrouter` |
| `shellcheck` | linting the two new bash scripts | ✗ | — | `bash -n` syntax check only; see below |
| Built `.lake/build` | gates 1–4 | ✗ **absent** | — | none — a build is required before any gate can run |
| Network | `gh`, `lake exe cache get`, `git fetch` | assumed ✓ (gh API calls succeeded this session) | — | — |

**Missing with no fallback:** a built Lean tree. Every gate task must be sequenced after a
successful `lake build`, and the plan should budget for it explicitly rather than treating it
as instantaneous.

**Missing with fallback:** `shellcheck`. Two new bash scripts with `set -euo pipefail`, arrays
and `gh` interpolation genuinely want it. Recommend the plan add an *optional* task:
`command -v shellcheck || pipx install shellcheck-py` — and if unavailable, fall back to
`bash -n` plus a manual read. Do **not** make an unavailable linter a blocker.

---

## Validation Architecture

This phase produces scripts and Markdown, not theorems. "Validated" means each deliverable was
*executed or parsed*, not merely written.

### Test framework

| Property | Value |
|----------|-------|
| Framework | none — no test harness exists for repository tooling. Validation is command execution with asserted output. |
| Config file | none. `lakefile.toml` declares a `Tests` lean_lib, deliberately **not** in `defaultTargets`; it covers `#guard_msgs` linter tests and Plausible property tests, not shell scripts. |
| Quick run command | `bash -n scripts/check-gates.sh && bash -n scripts/create-property-issues.sh && grep -rn <phantom> . --exclude-dir=.git --exclude-dir=.lake --exclude-dir=node_modules <scope>` |
| Full suite command | `./scripts/check-gates.sh` (all four gates, with baseline) + `./scripts/create-property-issues.sh` (dry-run, all IDs) |

### Phase requirements → validation map

| Req | Behaviour to demonstrate | Type | Command | Exists? |
|-----|--------------------------|------|---------|---------|
| INFRA-01 | Template names four gates by command + a catalog-and-index line | grep assertion | `grep -c '^- \[ \] \`lake' docs/ISSUE_TEMPLATE.md` → ≥3, and `grep -q 'print axioms' docs/ISSUE_TEMPLATE.md`, and `grep -q '§12' docs/ISSUE_TEMPLATE.md` | ❌ Wave 0 |
| INFRA-01 | The phantom token is gone from its scope | grep assertion | scoped grep (Q-1) returns empty, exit 1 | ❌ Wave 0 |
| INFRA-03 | Gate script is syntactically valid | static | `bash -n scripts/check-gates.sh` | ❌ Wave 0 |
| INFRA-03 | Gate script passes on a clean tree | integration | `./scripts/check-gates.sh spqr.kdf.hkdf_to_slice_spec; echo $?` → `0` | ❌ Wave 0 |
| INFRA-03 | Gate script **fails** on a deliberately broken tree — the only way to prove it is not a no-op | negative integration | see "Negative controls" below | ❌ Wave 0 |
| INFRA-03 | Its verdict matches CI's on `main` | cross-check | run on the `origin/main` worktree; compare each gate's verdict against the latest `main` "Lean Verification" run: `gh run list --workflow lean.yml --branch main --limit 1 --json conclusion` | ❌ Wave 0 |
| INFRA-02 | Issue script is syntactically valid and dry-runs | static + integration | `bash -n`, then `./scripts/create-property-issues.sh` with no `--execute` → prints titles+labels, **files nothing** (confirm open-issue count unchanged: `gh issue list --state open --limit 500 --json number --jq length` before and after) | ❌ Wave 0 |
| INFRA-02 | Generated body matches the template shape | diff | render one body to a file; assert every `{PLACEHOLDER}` from `docs/ISSUE_TEMPLATE.md` is substituted: `! grep -qE '\{[A-Z_]+\}' /tmp/body-PROP-42.md`; and that the four gate checklist lines are present | ❌ Wave 0 |
| INFRA-02 | Idempotent | integration | run `--execute` for one ID twice; second run prints `SKIP … already filed as #N`; issue count unchanged | ❌ Wave 0 |
| INFRA-02 | Labels created and correct | integration | `gh label list --limit 100 --json name --jq '[.[].name]'` contains all 15; re-running the label step is a no-op | ❌ Wave 0 |
| INFRA-02 | Rewording survives the roadmap parser | integration | `gsd-sdk query roadmap.get-phase 1` still returns the phase with 5 criteria after the ROADMAP edit | ❌ Wave 0 |
| CAT-01 | Template names the §12 index | grep | as INFRA-01 | ❌ Wave 0 |
| DEV-01..04 | §11 carries Decision + Status for all five rows | table parse | see the awk check below | ❌ Wave 0 |
| DEV-01..04 | PROP-42/30/43/47/50 each cite their D-row | grep | `for p in 42 30 43 47 50; do grep -A20 "^### PROP-$p " docs/spqr-properties.md \| grep -qE 'D[1-5]'; done` | ❌ Wave 0 |
| DEV-04 | The caller contract is under PROP-43 in §7 | grep | `grep -A30 '^### PROP-43' docs/spqr-properties.md \| grep -q 'caller'` | ❌ Wave 0 |

### The §11 table parse check

```bash
awk '/^## 11\./{f=1} /^## 12\./{f=0}
     f && /^\| D[1-5] \|/ {n=split($0,c,"|"); print $2, n}' docs/spqr-properties.md
```
Must print five rows, each with a consistent field count matching the header. Under
recommendation (b) (separate decision table), assert instead that the narrow table has five
`| D<n> | … | Provisional …|` rows and that every `Status` cell carries a date.

### Negative controls — the part that is easy to skip and most worth doing

A gate that has never failed is not known to work. For each gate, produce a failure once, in a
scratch worktree or a stashed change, and record the observed output in the phase SUMMARY:

| Gate | How to break it | Expected |
|------|-----------------|----------|
| 1 | add `def unusedFoo : Nat := 0` in a `Spqr/` file with an unused-variable or linter warning trigger | gate 1 FAIL, non-sorry warning printed |
| 2 | introduce a declaration the mathlib standard linter set rejects | gate 2 FAIL with an `error:` line |
| 3b | add a one-line theorem in a new `Spqr/Specs/` module closed by `sorry`, re-exported from `Spqr.lean` | gate 3b FAIL, the new decl listed as `direct` |
| 3b (silent-failure control) | same theorem in a module **not** re-exported from `Spqr.lean` | gate 3b **PASSES** — this is `Audit.lean`'s documented blind spot and the reason the template checklist gains a re-export line. Record it. |
| 4 | request `#print axioms` on a misspelled name | gate 4 FAIL with `unknown identifier`, not a silent pass |
| 4 | request a theorem transitively using `sorryAx` | gate 4 FAIL unless `--allow-sorry` |

### Sampling rate

- **Per task commit:** `bash -n` on any touched script + the scoped phantom grep + the §11
  parse check if the catalog changed. Seconds.
- **Per PR boundary (A and B):** full `./scripts/check-gates.sh`, issue-script dry-run over all
  IDs, and the complete requirement→validation table above.
- **Phase gate:** the negative controls run once, their output pasted into the SUMMARY, before
  `/gsd:verify-work`.

### Wave 0 gaps

- [ ] `scripts/check-gates.sh` — covers INFRA-03
- [ ] `scripts/axiom-allowlist.txt` — the gate-4 allowlist, INFRA-03
- [ ] `scripts/check-lint.sh` — rewritten as a shim (INFRA-03 compatibility)
- [ ] `scripts/create-property-issues.sh` + `scripts/property-issues.tsv` +
      `scripts/property-issue-labels.tsv` — covers INFRA-02
- [ ] `scripts/README.md` `## Verification gates` section — INFRA-03 documentation
- [ ] `.gitignore` — add `.gate-cache/`, `.sorry-delta-comment.md`; remove `issues/`
- [ ] `docs/signal-deviation-questions.md` — DEV-01..04 (D-11)
- [ ] A `lake build` of the working tree **and** of the baseline worktree, before any gate task
      can be validated
- [ ] No test framework needs installing — assertions are shell commands

---

## Security Domain

`security_enforcement` is absent from `.planning/config.json`, so it is enabled. This phase
writes no application code; the surface is the two shell scripts and the GitHub token.

### Applicable ASVS categories

| ASVS category | Applies | Standard control |
|---------------|---------|------------------|
| V2 Authentication | no | no auth code; `gh` handles its own token |
| V3 Session Management | no | — |
| V4 Access Control | partially | the `gh` token has `repo` scope, which can write to the repository. The issue script must never call anything other than `gh label create` and `gh issue create` — no `gh pr create` (PC-6), no `gh issue close/edit` (D-02). |
| V5 Input Validation | **yes** | property text from `docs/spqr-properties.md` flows into shell commands. Use `--body-file` with a temp file, quote every expansion, never `eval`. |
| V6 Cryptography | no | no crypto is written; the catalog *describes* crypto |
| V12 Files & Resources | yes | temp files for issue bodies and the gate-4 scratch Lean file: create with `mktemp -d` (0700), clean up on `trap … EXIT` |
| V14 Configuration | yes | secrets must not land in scripts: token from the `gh` keyring, Codex key from `~/.secrets/openrouter`, never inlined |

### Known threat patterns

| Pattern | STRIDE | Mitigation |
|---------|--------|------------|
| Command injection via property text containing `` ` ``, `$(…)`, `;` interpolated into a `gh` command string and `eval`d — the shape `issues/create_issues.sh:28-34` uses today | Elevation of privilege | `--body-file`; quote all expansions; no `eval`; `set -euo pipefail` |
| Path traversal via a `--repo`/worktree argument | Tampering | validate `--repo` against `^[A-Za-z0-9._-]+/[A-Za-z0-9._-]+$`; resolve worktree paths with `realpath` and refuse paths inside `$REPO_ROOT` |
| Unintended writes with a `repo`-scoped token (closing or editing existing issues, opening a PR) | Tampering | dry-run by default; `--execute` required; the script's `gh` allowlist is exactly `label create` and `issue create`; PC-6 forbids PR creation |
| Destructive cleanup (`rm -rf "$WT_DIR"` with an empty variable) | Denial of service | `${VAR:?must be set}` on every path variable before any `rm`; prefer `git worktree remove` over `rm -rf` |
| Stale/poisoned baseline manifest producing a false PASS | Spoofing | key the cache on the resolved SHA; `git fetch` before resolving; never fall back to the repo-root `sorry-manifest.txt` |
| Secret leakage into logs | Information disclosure | never `set -x` in the issue script; do not echo `gh auth token` |

---

## State of the Art

| Old approach (in-repo today) | Current approach (this phase) | Impact |
|---|---|---|
| `issues/create_issues.sh`: 45 heredoc'd issue bodies, `eval`, `\|\| true` label creation, `status:provable-now`/`tier:*` labels, references `docs/mlkembraid_spec/README.md` (gone) | template-driven generator + TSV, `--body-file`, `--force` labels, template label scheme, references `docs/spqr-properties.md` §12 | one source of truth; no injection; labels match catalog status one-to-one |
| `issues/SPQR_ISSUES_PREVIEW.md`: a 2119-line static preview of the bodies | `--dry-run` output of the live script | preview cannot drift from what gets filed |
| `scripts/check-lint.sh`: gates 1–2 only | `scripts/check-gates.sh`: gates 1–4 with a real `main` baseline | a property can actually be declared done locally |
| CI computes the sorry delta only on PRs, only as a comment | local delta with `SORRY_FAIL_ON_NEW=true` | failure before the PR, not after |
| Template checklist cites a non-existent gate | four runnable commands + `Spqr.lean` re-export + catalog/index line | INFRA-01 + CAT-01 |

**Deprecated / outdated in-tree:**
- `issues/272/README.md` documents seven `.lean` files that no longer exist.
- The root `sorry-manifest.txt` is a month-old build artifact (gitignored).
- `docs/STATE_INVARIANT_PROOFS.md` is gitignored (`.gitignore:33`) yet present on disk —
  untracked, out of scope, leave it alone.

---

## Package Legitimacy Audit

**Not applicable — this phase installs no external packages.** No `npm install`, `pip install`
or `cargo add` appears in any deliverable. Every tool the phase uses (`git`, `bash`, `python3`,
`gh`, `lake`, `lean`, `jq`) is already installed and version-verified in §Environment
Availability.

One optional, non-blocking exception: `shellcheck` is absent. If the planner adds a task to
install it, it must be gated behind `checkpoint:human-verify` and installed from the system
package manager (`apt install shellcheck`) rather than a language registry — `shellcheck` is a
Haskell binary and the PyPI `shellcheck-py` wrapper, while legitimate, is a registry dependency
this phase does not need. slopcheck was not run because no package is recommended.

---

## Assumptions Log

| # | Claim | Section | Risk if wrong |
|---|-------|---------|---------------|
| A1 | `#print axioms` output is `'<name>' depends on axioms: [a, b]` or `'<name>' does not depend on any axioms`, and an unknown name yields `unknown identifier`/`unknown constant` | Gate 4 | The gate-4 grep patterns are wrong and the gate silently passes. **Mitigation: the first gate-4 task must run the command once against a known theorem (`spqr.kdf.hkdf_to_slice_spec`) and paste the literal output into the plan/SUMMARY before writing the matcher.** Could not be verified here: the tree is unbuilt (B-5). |
| A2 | `opaque` declarations do not appear in `#print axioms` output (only `axiom`s do) | Gate 4 allowlist | `spqr.kdf.hkdf_to_slice` and `Spqr.Crypto.Hkdf.HMAC_SHA256` would need allowlist entries. Same mitigation as A1 — the empirical run settles both. |
| A3 | Cold-run cost of the baseline worktree is "tens of minutes with cache, hours without" | D-07 recipe | Task estimates are wrong. Measure and record. |
| A4 | GitHub's `in:title` search indexes titles promptly enough for same-session idempotency | Issue script | A second run within seconds of the first could re-file. Low risk given D-09's just-in-time cadence (issues filed minutes to days apart); belt-and-braces is to also re-list after filing. |
| A5 | `lake exe cache get` works for the mathlib revision aeneas pins | B-5 / worktree | Fallback is a from-source mathlib build. Verify on the first baseline run. |
| A6 | The plan reviewer and `spqr-eval` tolerate a phase with no Lean diff | Review gates | Both are written for theorem phases; a docs/scripts phase may read as thin. Mitigation: state the phase type explicitly in each plan's context block. |
| A7 | `gh label create --force` on a label that already exists with a *different* description does not error | Issue script | `--help` says it "updates an existing one"; not exercised here. Trivially recoverable. |

---

## Open Questions (RESOLVED)

All five were resolved during `/gsd-plan-phase 1` — Q-1 and Q-4 by the user, Q-2/Q-3/Q-5 by adopting the recommendation below. Each carries its resolution inline. None is still open.

### Q-1 — Success criterion 1's repo-wide grep cannot return empty (B-3)

- **RESOLVED (user, 2026-09-14): scope the grep.** Criterion 1 and INFRA-01 are reworded by plan 01-02 T1/T2. `.planning/PROJECT.md` and `.planning/STATE.md` are deliberately left alone — the user declined the belt-and-braces option. D-17's three operative files are still corrected (plan 01-01 T2).
- **What we know:** the token is in nine tracked files; six are `.planning/` records of the
  decision to remove it, including this phase's own CONTEXT and DISCUSSION-LOG, and the
  requirement and criterion that mandate the removal.
- **What's unclear:** whether the user wants the planning history rewritten, or the criterion
  scoped.
- **Recommendation:** **scope the grep**, and make the scoping an explicit ROADMAP edit in the
  same task that applies D-09's criterion-3 rewording. Proposed criterion 1:

  > `docs/ISSUE_TEMPLATE.md` names the four real gates (`lake build`,
  > `lake exe runLinter Spqr`, `lake env lean scripts/Audit.lean`, `#print axioms`) plus a
  > catalog-and-index update line; and
  > `git grep -n <phantom> -- ':!.planning'` returns nothing, so no *operative* document
  > (template, rubric, CLAUDE.md, scripts) cites a gate that does not exist. `.planning/` is
  > excluded because it is the append-only record of the decision to remove the token.

  `git grep -- ':!.planning'` is exact, respects tracked-file boundaries, and is a single
  command a verifier can run. Also reword INFRA-01 to "instead of a gate that does not exist in
  the repository" so the requirement stops naming the token. This keeps D-17 intact (its three
  files are still corrected) and adds `.planning/PROJECT.md:67` and `.planning/STATE.md:66`
  only if the user prefers belt-and-braces — both are one-line rewordings and cost nothing.

### Q-2 — What is PR A's base branch? (B-4)

- **RESOLVED (default adopted): stack on `la/spec-catalog`, but do not decide silently.** The question is carried verbatim and marked OPEN in plan 01-07 T3's stop-and-report text, for the user to answer at the PR A boundary.
- **What we know:** `main` contains none of the files this phase edits; `la/spec-catalog` is
  unmerged and has diverged from its remote; `branching_strategy` is `none`.
- **What's unclear:** whether the user intends to merge `la/spec-catalog` to `main` first, or
  stack PR A and PR B on it.
- **Recommendation:** default to stacking on `la/spec-catalog` (PR A → `la/spec-catalog`,
  PR B → PR A's branch) and **raise it at the first PR-boundary report** rather than deciding
  silently. The planner should put this question in PR A's stop-and-report task text verbatim.

### Q-3 — Does the `issues/272/` analysis survive deletion?

- **RESOLVED (recommendation adopted): ask before deleting.** Plan 01-05 T1 is a blocking `checkpoint:decision` that runs `gh issue view 272` and asks the user, preceding the `rm -rf`.
- **What we know:** the README documents a real, load-bearing finding (a false postcondition in
  `Spqr/Specs/Encoding/Polynomial/LagrangePolysForCompletePoints.lean:40`, with a fix on
  `fix/272-frame-condition-loop0-body-spec`). The supporting `.lean` files are already gone.

  > **Correction (plan review 01, 2026-09-14): this describes a past state of the tree, not
  > the current one.** `LagrangePolysForCompletePoints.lean` today has **no `sorry`**:
  > `body_spec` at `:47` closes with `unfold body` and the frame conclusion at `:57` is
  > `(ones1[i]!).y = (ones[i]!).y` — it *preserves* the `y` field rather than asserting
  > `GF16.ONE`, and the doc comment at `:40-43` explains that callers recover
  > `y = GF16.ONE` by composing this frame with their own invariant, which
  > `lagrange_polys_for_complete_points_spec` does. So the `issues/272/README.md` analysis is
  > **historical**. Treat it as such when deciding its fate: it documents a defect that has
  > since been addressed, which is an argument for posting it to the issue thread as a record
  > and closing it out, not for preserving it as live analysis.
- **What's unclear:** whether it has been posted to issue #272.
- **Recommendation:** before deleting, `gh issue view 272` and, if the analysis is not in the
  thread, offer to post it as a comment (a comment is not a PR, so PC-6 is untouched — but ask
  first). This is a one-task addition and it prevents a silent loss. It also touches AXIOM-04's
  Phase 4 scope.

### Q-4 — §11 layout: one wide table or two? (D-12)

- **RESOLVED (user, 2026-09-14): two tables (option b).** The five-column table and its five rows stay verbatim; a narrow `| ID | Decision | Status |` table is added beneath. Plan 01-08's `<layout_decision>` block states this reading of D-12 and its reasoning explicitly, so the Codex plan reviewer does not file it as drift.
- **Recommendation:** two tables (option (b) above). The planner should state the choice and
  its reasoning in the plan so the reviewer reads it as a deliberate reading of D-12, not drift.

### Q-5 — Does gate 4 belong in CI eventually?

- **RESOLVED (recommendation adopted): no action this phase.** Filed as a `type:proof-infra` TSV row (`INFRA-CI-GATE4`) during PR A's run, so the deferred idea is tracked rather than lost.
- **What we know:** D-08a scopes this phase to local-only and the CONTEXT defers the
  `lean.yml` refactor.
- **Recommendation:** no action this phase. File it as a `type:proof-infra` issue during PR A's
  run so the deferred idea is tracked rather than lost — D-04 already says INFRA deliverables
  get issues, and this costs one TSV row.

---

## Sources

### Primary (HIGH confidence — read in this session)
- `.github/workflows/lean.yml`, `.github/workflows/sorry-delta-comment.yml` — the four gate
  steps, cache keys, artifact upload, `LEAN_ABORT_ON_PANIC`
- `scripts/check-lint.sh`, `scripts/Audit.lean` (full), `scripts/sorry-diff.py` (full),
  `scripts/README.md`
- `sorry-manifest.txt` — format and current contents (134 lines, 36 `Spqr.Specs.*`)
- `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `.gitignore`
- `SrcTranslated/FunsExternal.lean` (**173 `axiom` + 1 `opaque`** declarations; the earlier
  "55" in this inventory was wrong — corrected at plan review 01, 2026-09-14. Note the
  allowlist is deliberately far smaller than this inventory: it admits 17 documented stubs,
  not every extracted axiom, so a theorem reaching a prost or `core.*` axiom fails gate 4 by
  design. Namespace structure as described in the gate-4 traps below.),
  `SrcTranslated/Funs.lean` (`namespace spqr`, `def initial_state/send/recv`)
- `Spqr/Specs/Kdf/HkdfToSlice.lean`, `Spqr/Crypto/Hkdf.lean`, `Spqr.lean`
- `docs/spqr-properties.md` (§1, §5, §7, §8, §11, §12, §13), `docs/ISSUE_TEMPLATE.md` (full),
  `docs/rubrics/spqr-plan-review.md` (full)
- `src/lib.rs:356-455`, `src/v1/unchunked/send_ct.rs:104-114`,
  `src/v1/unchunked/send_ek.rs:145-175`, `src/authenticator.rs:44-90`
- `issues/create_issues.sh`, `issues/SPQR_ISSUES_PREVIEW.md`, `issues/272/README.md`
- `CLAUDE.md`, `.planning/{PROJECT,REQUIREMENTS,ROADMAP,STATE}.md`, `.planning/config.json`,
  `.planning/phases/01-…/01-CONTEXT.md`
- `.claude/agents/spqr-eval.md`, `.claude/skills/spqr-plan-review/SKILL.md`
- `.lake/packages/batteries/lakefile.toml`, `.lake/packages/mathlib/lakefile.lean`

### Primary (HIGH confidence — commands run in this session)
- `git check-ignore -v`, `git ls-files`, `git diff --stat origin/main..HEAD`,
  `git worktree list`, `git rev-parse origin/main`, `git remote -v`
- `grep -rn <phantom> .` (nine hits), `grep -rn "issues/"` (no internal path references)
- `gh --version`, `gh auth status`, `gh label list --limit 100`, `gh issue list`,
  `gh issue view 44`, `gh pr view 541`, `gh issue list --search … in:title`,
  `gh label create --help`
- `gsd-sdk query init.phase-op 1`, `gsd-tools requirements`, `gsd-tools roadmap`,
  `gsd-tools --help`
- `lake --version`, `lean --version`, `command -v` probes, `df -h`,
  `find .lake -name '*.olean'`

### Secondary (MEDIUM confidence)
- SDK source under `~/.npm/_npx/.../get-shit-done-cc/sdk/src/query/` — command manifests
  confirming the absence of a requirements/roadmap text-edit handler (source read, not a
  published API contract)

### Tertiary (LOW confidence — flagged in the Assumptions Log)
- `#print axioms` output format and `opaque` invisibility (A1, A2) — training knowledge;
  `scripts/Audit.lean`'s header cites
  `https://lean-lang.org/doc/reference/latest/ValidatingProofs/` but the page was not fetched
  and the command was not run (unbuilt tree). Must be confirmed empirically in Wave 0.
- Cold-build cost estimates (A3) — not measured.

---

## Metadata

**Confidence breakdown:**
- Gate mechanics: **HIGH** — every command, log path, exit convention and file format read
  directly from CI and the scripts. The one gap is gate 4's output format (A1/A2), which has no
  in-repo precedent and could not be run.
- Issue tooling: **HIGH** — template, old script, label inventory, auth state and search
  behaviour all probed live against the real repository.
- Catalog surgery: **HIGH** — every line quoted from the file at `f44568b`; `src/` evidence for
  D5 read at the pinned commit `d47083c` (= `origin/main`).
- Blockers B-1..B-5: **HIGH** — each verified by a command whose output is reproduced above.
- Cold-build cost and gate-4 output format: **LOW** — see Assumptions Log.

**Research date:** 2026-09-14
**Valid until:** 2026-10-14 for the repository facts (stable, no external dependencies). The
`gh` state (issue numbers, label list, the 53 open issues) is live and can change at any time —
the issue script must query it rather than trust these numbers.
