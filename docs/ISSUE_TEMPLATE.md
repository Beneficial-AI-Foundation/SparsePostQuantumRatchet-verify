# SPQR Property — Issue Template

Use this template to create a GitHub issue for a single property (or grouped companion
pair) from `docs/SPQR_LEAN_PROPERTIES.md`.

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

**Source:** {SOURCES}

<!-- Comma-separated source tags. Choose from:
  - production-code
  - production-test
  - spec-mlkembraid (include section, e.g. §2.5)
  - spec-2025-2267
  - hax-cross
  - hax-kat
  - hax-proptest
  - lean-specific
-->

**Tier:** {TIER}

<!-- Choose one:
  - 1: Provable Now
  - 2: Axiom-Backed
  - 3: Infrastructure Work
  - 4: Blocked
  - Proved
-->

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

<!-- The Lean theorem/axiom statement.
     For axioms: use `axiom` keyword.
     For theorems: use `theorem` keyword with full signature.
     Include precondition hypotheses and postcondition in WP style:
       theorem name (args...) (h : precondition) :
           function args ⦃ result => postcondition ⦄
-->

### Lean Provability

- **Difficulty:** {DIFFICULTY}
  <!-- Easy / Medium / Hard / Axiom-only -->

- **Status:** {STATUS}
  <!-- Provable Now / Feasible / Axiom Required / Blocked / Proved -->

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
       - Blockers (e.g. "lib.rs not extracted")
       - "None" if self-contained
  -->

### Checklist

- [ ] Lean theorem statement written
- [ ] Proof completed
- [ ] `#check_no_sorry` passes
- [ ] Added to proof file index in `SPQR_LEAN_PROPERTIES.md`

<!-- Add additional checklist items as needed, e.g.:
- [ ] Blocker resolved (describe)
- [ ] Axiom prerequisites stated
- [ ] Spec deviation documented in proof comments
- [ ] All case-analysis arms verified
- [ ] Helper lemmas proved (list them)
-->

---

### Labels

<!-- Suggested labels for this issue (used by create_issues.sh):

Type (pick one):
  type:algebraic-spec | type:state-invariant | type:behavioral-spec |
  type:correspondence | type:serialization | type:deviation-flag |
  type:history-erasure | type:progress | type:proof-infra

Status (pick one):
  status:provable-now | status:feasible | status:axiom-required |
  status:blocked | status:proved

Tier (pick one):
  tier:1 | tier:2 | tier:3 | tier:4 | tier:proved

Special (if applicable):
  modelling-assumption | spec-deviation
-->

**Labels:** `{TYPE_LABEL}`, `{STATUS_LABEL}`, `{TIER_LABEL}`
