# Superseded Phase 1 plan set — archived 2026-09-15

The nine plans here were planned and reviewed (round 1 REJECT, round 2
APPROVE-WITH-EDITS, see `01-CODEX-REVIEW.md` and `01-CODEX-REVIEW-2.md` in the
phase directory) against the original goal: close every Open catalog row, with
one GitHub issue per property.

They were superseded before execution by the 2026-09-15 re-scope: the goal
became *prove as many non-trivial specs as possible*, with provenance (PROV-01)
and a binding statement review (REV-01), and automated issue creation was
dropped.

What carried forward into the new plan set:
- 01-01 (gate documentation, phantom `#check_no_sorry` removal) → new 01-01,
  repointed from an issue template to a PR checklist
- 01-03 (`scripts/check-gates.sh`, axiom allowlist) → new 01-02, extended with
  the fifth provenance gate
- 01-06 (build, run gates, negative controls, CI cross-check) → new 01-04
- 01-08 (§11 D1–D5 decisions, property restatements) → new 01-08

What was dropped:
- 01-02 (reword INFRA-01/02 and ROADMAP criteria) — absorbed; `REQUIREMENTS.md`
  and `ROADMAP.md` were rewritten directly in the re-scope
- 01-04 (`scripts/create-property-issues.sh` + TSVs) — issue automation, out of scope
- 01-05 (retire the legacy `issues/` tooling) — moot once no issue tooling is built;
  `issues/` stays untracked and gitignored
- 01-07 (create labels, file the PR A issues) — issue filing, out of scope
- 01-09 (Signal deviation note, DEV issue filing) — the note is deferred to v2 (DEV-05)

The Codex review findings that still applied were carried into the new plans:
the multiline-axiom-declaration predicate (round 2 F-4), the non-waivable
wrapped-axiom-list control (F-6), the PR-range and branch-boundary handling
(F-1), and the declared-wave/DAG sync (F-5).
