<!-- GSD:project-start source:PROJECT.md -->
## Project

**SPQR Property Proofs**

A proof effort against the SPQR (Sparse Post-Quantum Ratchet) correctness
catalog in `docs/spqr-properties.md`. The goal is to prove as many catalog
specifications as possible in Lean, concentrating on the ones that say
something beyond the single-function functional correctness this repository has
already dealt with. Every spec proved must carry a resolvable source citation
and must pass a statement review before any proof work starts. The audience is
the verification team working on this repository and the Signal reviewers who
read the catalog.

**Core Value:** A proved property has all three: a Lean theorem with no `sorry` and
no hand-written axiom beyond the documented opaque stubs; a source citation that
resolves to the ML-KEM Braid spec, the SCKA paper or `src/` at `d47083c`; and an
ACCEPT statement review recorded *before* the proof was written.

### Target Selection

A catalog row is a proof target iff it passes all three:

- **C1 — not already proved.** No theorem on `main`; a partially proved row qualifies for its open half.
- **C2 — not invented.** Traceable to the ML-KEM Braid spec, the SCKA paper, or the code. Enforced by PROV-01, adjudicated per statement by REV-01.
- **C3 — not trivial.** Measured by what the statement *ranges over*, not by expected proof effort:

| Band | Ranges over | In scope |
|------|-------------|----------|
| Evaluation | a closed term equals a literal | no — support only |
| Single path | one function, one branch | no — support only |
| Whole structure | an entire encoding or data structure: roundtrip, injectivity, canonicity | **yes** |
| Multi-site invariant | every call site that reaches a point | **yes** |
| Refinement | the code's state machine against the spec's | **yes** |
| Trace / cross-party | runs across epochs, and both parties | **yes** |

Excluded-band rows are **support lemmas**: proved when a target needs them, never a
phase goal. They are out of the goal, not out of scope. Promoting one to a phase
goal is a scope error.

### Constraints

- **Trusted base**: no new hand-written axiom without a catalog entry explaining why it cannot be a theorem — the Core Value depends on this
- **Provenance (PROV-01)**: every catalog row carries a `Source:` citation naming **at least one** of ML-KEM Braid Rev. 1 §x.y, SCKA Def./Fig. n, or `src/path.rs:lines` at `d47083c` — semicolon-separated when a row has both a spec ground and the code implementing it — and the provenance gate fails on **any** listed citation that does not resolve. Pointers outside those three classes (a `Spqr/Specs/**` lemma, a planning doc) go on a separate `Evidence:` line, outside the gate's grammar. Theorem statements must match the catalog wording; if a statement must change, the catalog changes in the same PR
- **Statement review (REV-01)**: no proof work on an unreviewed statement. Before a property's proof, an independent cross-engine read-only reviewer gets the proposed Lean statement plus only its cited source and returns ACCEPT / REVISE / REJECT against C1, C2 and C3. Recorded per property in a tracked log; no ACCEPT means no proof work; disputes stop for the user. A correct theorem proved without a prior ACCEPT is still a process failure
- **Process**: one draft PR per property, following the #537–#541 pattern. **No GitHub issues** — the PR is the unit of work; issue automation was dropped 2026-09-15. The user opens every PR themselves: when a property's work is complete and verified, GSD stops and reports; the user creates the PR, then work continues with the next property
- **Review gates**: after `/gsd-plan-phase N` and before `/gsd-execute-phase N`, run `/spqr-plan-review N` (Codex, read-only, rubric `docs/rubrics/spqr-plan-review.md`); only APPROVE, or APPROVE-WITH-EDITS with all edits triaged and applied, routes to execution. After execution, alongside gsd-verifier, dispatch the `spqr-eval` agent (`.claude/agents/spqr-eval.md`) on the phase diff; persist as `NN-EVAL.md`; FOLLOWUP routes to a gap-closure plan, HUMAN_RULING stops for the user
- **Gates**: five checks — `lake build` with no non-sorry warning, `lake exe runLinter Spqr`, `lake env lean scripts/Audit.lean`, `#print axioms` against the allowlist, and the provenance check; `scripts/check-gates.sh` runs all five. `docs/ISSUE_TEMPLATE.md` is the per-property **PR** checklist naming them; the gate it used to cite does not exist in this repository and was removed in Phase 1
- **Tooling**: proofs must build with the repository's pinned Lean/Aeneas versions; no toolchain bumps inside a property PR
- **Code freeze**: `src/` changes are limited to D1–D5 resolutions agreed with Signal
- **Dependencies**: PROP-1 needs PROP-3 (axiom) and PROP-24; PROP-23 and PROP-50 need the per-transition results of PROP-47; PROP-38 and PROP-37 depend on prost `sorry`s and may end as trusted rather than proved; PROP-35's roundtrip needs a `varintBytes`-to-`varintBlockAt` agreement lemma that does not yet exist
- **Known catalog gap**: every roundtrip row states only `decode(encode(x)) = x`. The converse is nowhere, and for the wire format it appears false — `Spqr/Specs/V1/Chunked/States/Serialize/DecodeVarint.lean:43` records that `decode_varint` accepts non-canonical LEB128. Two new rows cover this; a negative result is a valid outcome
<!-- GSD:project-end -->

<!-- GSD:stack-start source:STACK.md -->
## Technology Stack

- Rust crate under `src/` (SPQR, pinned at `d47083c`); never edited outside a D1–D5 decision.
- Aeneas (`nightly-2026.08.27-5b9dcf3`) extracts the whole crate into `SrcTranslated/` (`Funs.lean`, `Types.lean`, `FunsExternal.lean` axiom stubs). Never hand-edited.
- Lean `leanprover/lean4:v4.31.0`, build with `lake build` (default targets `Spqr`, `SrcTranslated`); hand-written specs and proofs under `Spqr/Specs/`, every module re-exported from `Spqr.lean`.
- Gates (five, run by `scripts/check-gates.sh`): `lake build` with no warning other than `declaration uses 'sorry'`; `lake exe runLinter Spqr`; `lake env lean scripts/Audit.lean` (axiom audit, writes `sorry-manifest.txt`); `#print axioms <thm>` against `scripts/axiom-allowlist.txt`; the provenance check over `docs/spqr-properties.md` `Source:` citations.
- Sources for provenance: ML-KEM Braid Rev. 1 (`mlkembraid.pdf`); SCKA — Auerbach, Dodis, Jost, Katsumata, Schmidt (`2025-2267.pdf`), Def. 3.1 and Fig. 1–2; the code at `d47083c`.
<!-- GSD:stack-end -->

<!-- GSD:conventions-start source:CONVENTIONS.md -->
## Conventions

- One spec file per Rust function: `Spqr/Specs/<Module>/<Type>/<Function>.lean`, header comment naming the Rust path, `@[step] theorem <fn>_spec ... : f args ⦃ r => P r ⦄` in WP style over `Result`. See `Spqr/Specs/Chain/Chain/AddEpoch.lean` (PR #541) for the pattern.
- One draft PR per catalog property; the user opens the PRs. No GitHub issues. `docs/ISSUE_TEMPLATE.md` is the per-property PR checklist. The catalog row, section text and §12 index change in the same PR as the theorem.
- Every catalog row carries a `Source:` citation; every proved row carries a reference to its ACCEPT statement review.
- Property IDs (`PROP-n`, `LEAN-*`, `STRUCT-*`, `D1`–`D5`) are stable; use them in commits, PR titles and theorem doc-comments.
- The selection record is `docs/proof-targets.md`: band, C1/C2/C3 verdict, source and support dependencies for every row.
<!-- GSD:conventions-end -->

<!-- GSD:architecture-start source:ARCHITECTURE.md -->
## Architecture

Three layers, as in `docs/spqr-properties.md` §1: the SCKA interface (§1.1 of the ML-KEM Braid spec; trace properties over `lib.rs` `send`/`recv`), ML-KEM Braid (`src/v1/` eleven-variant `States` machine, `authenticator.rs`, `incremental_mlkem768.rs`, `encoding/`), and the chain/API compiler (`chain.rs`, `lib.rs`). Opaque items: libcrux KEM/HMAC stubs, `hkdf_to_slice` (single hand-written axiom), `PolyDecoder.decoded_message`, prost `Message` impls (`sorry`). Proofs on `la/lean-v1-protocol-proofs` (`States/Send.lean`, `States/Recv.lean`, liveness axioms in `Specs/External.lean`) are not yet on `main`.

Where the targets live by band: **whole structure** in `encoding/` and the serialize/protobuf paths plus `chain.rs` GC; **multi-site** at the two KDF_OK sites and the four paths reaching `Ct1Sent::recv_ek`; **refinement** in the `src/v1/chunked/states.rs` 13-transition table; **trace** over `lib.rs` `send`/`recv` across epochs and across both parties.
<!-- GSD:architecture-end -->

<!-- GSD:skills-start source:skills/ -->
## Project Skills

| Skill | Description | Path |
|-------|-------------|------|
| spqr-plan-review | Independent adversarial Codex review of a GSD phase's plan set before execution, per docs/rubrics/spqr-plan-review.md. Use after /gsd-plan-phase N and before /gsd-execute-phase N, e.g. "/spqr-plan-review 3". | `.claude/skills/spqr-plan-review/SKILL.md` |
| spqr-statement-review | REV-01: independent cross-engine review of one property's proposed Lean statement against only its cited source, ruling ACCEPT / REVISE / REJECT on C1, C2 and C3. Run before any proof work on that property. Built in Phase 1. | `.claude/skills/spqr-statement-review/SKILL.md` |
<!-- GSD:skills-end -->

<!-- GSD:workflow-start source:GSD defaults -->
## GSD Workflow Enforcement

Before using Edit, Write, or other file-changing tools, start work through a GSD command so planning artifacts and execution context stay in sync.

Use these entry points:
- `/gsd-quick` for small fixes, doc updates, and ad-hoc tasks
- `/gsd-debug` for investigation and bug fixing
- `/gsd-execute-phase` for planned phase work

Do not make direct repo edits outside a GSD workflow unless the user explicitly asks to bypass it.
<!-- GSD:workflow-end -->



<!-- GSD:profile-start -->
## Developer Profile

> Profile not yet configured. Run `/gsd-profile-user` to generate your developer profile.
> This section is managed by `generate-claude-profile` -- do not edit manually.
<!-- GSD:profile-end -->
