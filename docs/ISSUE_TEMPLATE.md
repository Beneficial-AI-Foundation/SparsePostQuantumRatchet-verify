# SPQR Property — PR Checklist

Use this document as the checklist for the draft PR that proves one property (or grouped
companion pair) from `docs/spqr-properties.md`. The PR is the unit of work on this project:
there are no GitHub issues and no label vocabulary to fill in. One property, one draft PR.

---

## Property: {PROP-ID}

<!-- Replace {PROP-ID} with the property identifier, e.g. PROP-9, PROP-15/15b, LEAN-GF-6/7 -->

**Type:** {TYPE}

<!-- Choose one:
  - State Invariant
  - Conditional Behavioral Spec
  - Algebraic Specification
  - Correspondence Property
  - Serialization
  - Deviation Flag
  - History / Erasure
  - Progress / Injectivity
  - Proof Infrastructure
-->

**Band:** {BAND}

<!-- The C3 band recorded for this obligation in `docs/proof-targets.md`:
  - Whole structure | Multi-site invariant | Refinement | Trace / cross-party — a target
  - Evaluation | Single path — a support lemma, proved when a target needs it and never a
    phase goal; it does not go through the target route (see the preconditions below)
-->

**Source:** {SOURCES}

<!-- PROV-01 grammar — at least one of:
  - ML-KEM Braid Rev. 1 §x.y
  - SCKA Def. n / Fig. n
  - src/path.rs:lines, at d47083c
  Semicolon-separated when the row has both a spec ground and the code implementing it.
  Every listed citation must resolve; the provenance gate fails on any that does not.
  Pointers outside those three classes (a Spqr/Specs/** lemma, a planning document) belong
  on a separate `Evidence:` line, which is outside the gate's grammar.
-->

**Evidence:** {EVIDENCE}

<!-- Optional. Supporting pointers that are not PROV-01 sources. "None" if unused. -->

---

### Description

{DESCRIPTION}

<!-- Informal English description of what the property asserts.
     Include:
     - Preconditions
     - What it guarantees (postcondition / error / invariant)
     - Caveats or soundness flags
     - Spec deviation notes (if applicable)
     - Relationship to other properties (duals, dependencies)
-->

### Formal Definition

```lean
{LEAN_STATEMENT}
```

<!-- The Lean theorem/axiom statement, verbatim as reviewed under REV-01.
     For axioms: use `axiom` keyword.
     For theorems: use `theorem` keyword with full signature.
     Include precondition hypotheses and postcondition in WP style:
       theorem name (args...) (h : precondition) :
           function args ⦃ result => postcondition ⦄
     The statement must match the catalog wording; if it has to change, the catalog row
     changes in this same PR.
-->

### Lean Provability

- **Difficulty:** {DIFFICULTY}
  <!-- Easy / Medium / Hard / Axiom-only -->

- **Status:** {STATUS}
  <!-- One of the values used in docs/spqr-properties.md:
       Proved / Proved (branch) / Open / Axiom -->

- **Proof approach:** {APPROACH}
  <!-- Brief description of the proof strategy, e.g.:
       - "unfold + step*"
       - "case-split over 11 variants"
       - "structural induction on byte array"
       - "instantiate PROP-4 axiom with ..."
  -->

- **Dependencies:** {DEPENDENCIES}
  <!-- List of:
       - Required axioms (e.g. "PROP-4 collision-infeasibility")
       - Prerequisite properties (e.g. "PROP-9, PROP-29")
       - Support lemmas this proof needs (list them)
       - Blockers (e.g. "lib.rs not extracted")
       - "None" if self-contained
  -->

---

### Checklist — preconditions (before any proof work)

- [ ] The obligation is recorded as a target in `docs/proof-targets.md`, with its band and
      its C1/C2/C3 verdict.
- [ ] Its `Source:` citation is in `docs/spqr-properties.md` and resolves (PROV-01).
- [ ] An **ACCEPT** statement review for this exact statement is recorded in
      `docs/spec-review-log.md`, dated **before** the first proof commit (REV-01). No
      ACCEPT means no proof work; a correct theorem proved without a prior ACCEPT is still
      a process failure.
- [ ] Every **support lemma** proved along the way has its own `scope: support` ACCEPT
      (`/spqr-statement-review <ID> --support`), not a target ACCEPT. Support lemmas sit in
      an excluded band, so the target-only route does not apply to them, and they must not
      be counted as targets.

### Checklist — gates (before the PR is opened)

- [ ] `lake build` — no warning other than `declaration uses 'sorry'`.
- [ ] `lake exe runLinter Spqr` — no `error:`.
- [ ] `lake env lean scripts/Audit.lean` — no new line in `sorry-manifest.txt`.
- [ ] `#print axioms <theorem>` — only builtins and `scripts/axiom-allowlist.txt` entries.
- [ ] `python3 scripts/check-provenance.py` — the row's `Source:` citation resolves.
- [ ] The new module is re-exported from `Spqr.lean`. `scripts/Audit.lean` cannot see a
      module that is not reachable from the root, so an unexported proof passes the audit
      gate vacuously.
- [ ] The property's status row, its section text and the **§12 index** in
      `docs/spqr-properties.md` are all updated in this same PR (CAT-01).

One command for all five gates:

```bash
./scripts/check-gates.sh <theorem-names>
```

<!-- Add additional checklist items as needed, e.g.:
- [ ] Blocker resolved (describe)
- [ ] Axiom prerequisites stated
- [ ] Spec deviation documented in proof comments
- [ ] All case-analysis arms verified
-->

---

The PR itself is opened by the user, as a draft, following the #537–#541 pattern: when the
property's work is complete and the gates pass, work stops and reports.
