<!-- GSD:project-start source:PROJECT.md -->
## Project

**SPQR Property Proofs**

A proof roadmap for the SPQR (Sparse Post-Quantum Ratchet) correctness
catalog in `docs/spqr-properties.md`. It takes every property whose status is
Open to a `sorry`-free Lean theorem on `main`, brings the theorems that exist
only on `la/lean-v1-protocol-proofs` onto `main`, reduces the trusted base to
the documented opaque stubs, and tracks the five spec-vs-code deviations as
decisions rather than proofs. The audience is the verification team working on
this repository and the Signal reviewers who read the catalog.

**Core Value:** Every status in the catalog can be regenerated from the Lean sources on
`main`: a property marked Proved has a theorem with no `sorry` and no
hand-written axiom beyond the documented opaque stubs.

### Constraints

- **Trusted base**: no new hand-written axiom without a catalog entry explaining why it cannot be a theorem — the Core Value depends on this
- **Provenance**: theorem statements must match the catalog wording; if a statement must change, the catalog changes in the same PR
- **Process**: one GitHub issue per property (from `docs/ISSUE_TEMPLATE.md`), one draft PR per issue closing it, following the #537–#541 pattern. The user opens every PR themselves: when a property's work is complete and verified, GSD stops and reports; the user creates the PR, then work continues with the next property
- **Review gates**: after `/gsd:plan-phase N` and before `/gsd:execute-phase N`, run `/spqr-plan-review N` (Codex, read-only, rubric `docs/rubrics/spqr-plan-review.md`); only APPROVE, or APPROVE-WITH-EDITS with all edits triaged and applied, routes to execution. After execution, alongside gsd-verifier, dispatch the `spqr-eval` agent (`.claude/agents/spqr-eval.md`) on the phase diff; persist as `NN-EVAL.md`; FOLLOWUP routes to a gap-closure plan, HUMAN_RULING stops for the user
- **Gates**: `#check_no_sorry` in `docs/ISSUE_TEMPLATE.md` does not exist in the repo; the real checks are `lake build` with no non-sorry warning, `lake exe runLinter Spqr`, `lake env lean scripts/Audit.lean`, and `#print axioms`. The template should be corrected in the first phase
- **Tooling**: proofs must build with the repository's pinned Lean/Aeneas versions; no toolchain bumps inside a property PR
- **Code freeze**: `src/` changes are limited to D1–D5 resolutions agreed with Signal
- **Dependencies**: PROP-1 needs PROP-3 (axiom) and PROP-24; PROP-23 and PROP-50 need the per-transition results of PROP-47; PROP-38 and PROP-37 depend on prost `sorry`s and may end as trusted rather than proved
<!-- GSD:project-end -->

<!-- GSD:stack-start source:STACK.md -->
## Technology Stack

- Rust crate under `src/` (SPQR, pinned at `d47083c`); never edited outside a D1–D5 decision.
- Aeneas (`nightly-2026.08.27-5b9dcf3`) extracts the whole crate into `SrcTranslated/` (`Funs.lean`, `Types.lean`, `FunsExternal.lean` axiom stubs). Never hand-edited.
- Lean `leanprover/lean4:v4.31.0`, build with `lake build` (default targets `Spqr`, `SrcTranslated`); hand-written specs and proofs under `Spqr/Specs/`, every module re-exported from `Spqr.lean`.
- Gates: `lake build` with no warning other than `declaration uses 'sorry'`; `lake exe runLinter Spqr`; `lake env lean scripts/Audit.lean` (axiom audit, writes `sorry-manifest.txt`); `#print axioms <thm>`.
<!-- GSD:stack-end -->

<!-- GSD:conventions-start source:CONVENTIONS.md -->
## Conventions

- One spec file per Rust function: `Spqr/Specs/<Module>/<Type>/<Function>.lean`, header comment naming the Rust path, `@[step] theorem <fn>_spec ... : f args ⦃ r => P r ⦄` in WP style over `Result`. See `Spqr/Specs/Chain/Chain/AddEpoch.lean` (PR #541) for the pattern.
- One GitHub issue per catalog property (`docs/ISSUE_TEMPLATE.md`), one draft PR per issue; the user opens the PRs. The catalog row, section text and §12 index change in the same PR as the theorem.
- Property IDs (`PROP-n`, `LEAN-*`, `D1`–`D5`) are stable; use them in commits, issues and theorem doc-comments.
<!-- GSD:conventions-end -->

<!-- GSD:architecture-start source:ARCHITECTURE.md -->
## Architecture

Three layers, as in `docs/spqr-properties.md` §1: the SCKA interface (§1.1 of the ML-KEM Braid spec; trace properties over `lib.rs` `send`/`recv`), ML-KEM Braid (`src/v1/` eleven-variant `States` machine, `authenticator.rs`, `incremental_mlkem768.rs`, `encoding/`), and the chain/API compiler (`chain.rs`, `lib.rs`). Opaque items: libcrux KEM/HMAC stubs, `hkdf_to_slice` (single hand-written axiom), `PolyDecoder.decoded_message`, prost `Message` impls (`sorry`). Proofs on `la/lean-v1-protocol-proofs` (`States/Send.lean`, `States/Recv.lean`, liveness axioms in `Specs/External.lean`) are not yet on `main`.
<!-- GSD:architecture-end -->

<!-- GSD:skills-start source:skills/ -->
## Project Skills

| Skill | Description | Path |
|-------|-------------|------|
| spqr-plan-review | Independent adversarial Codex review of a GSD phase's plan set before execution, per docs/rubrics/spqr-plan-review.md. Use after /gsd:plan-phase N and before /gsd:execute-phase N, e.g. "/spqr-plan-review 3". | `.claude/skills/spqr-plan-review/SKILL.md` |
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
