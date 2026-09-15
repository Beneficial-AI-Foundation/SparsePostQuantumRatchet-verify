# SPQR Property Proofs

## What This Is

A proof effort against the SPQR (Sparse Post-Quantum Ratchet) correctness
catalog in `docs/spqr-properties.md`. The goal is to prove as many catalog
specifications as possible in Lean, concentrating on the ones that say
something beyond the single-function functional correctness this repository has
already dealt with. Every spec proved must carry a resolvable source citation
and must pass a statement review before any proof work starts. The audience is
the verification team working on this repository and the Signal reviewers who
read the catalog.

## Core Value

A proved property is one where all three hold: a Lean theorem with no `sorry`
and no hand-written axiom beyond the documented opaque stubs; a source citation
that resolves to the ML-KEM Braid spec, the SCKA paper or `src/` at `d47083c`;
and an ACCEPT verdict from an independent statement review recorded before the
proof was written.

## Target Selection

A catalog row is a proof target iff it passes all three criteria:

- **C1 — not already proved.** No theorem for it on `main`. Partially proved
  rows qualify for their open half. **The unit of selection is the open
  obligation, not the catalog row** (ruled 2026-09-15): `docs/proof-targets.md`
  records the obligation, a row's proved half is recorded as out of the goal, and
  a row may contribute more than one unit or none. This is why the 22 targets do
  not correspond one-to-one with rows.
- **C2 — not invented.** The statement is traceable to the ML-KEM Braid spec,
  the SCKA paper, or the code itself. Enforced by PROV-01 and checked by the
  provenance gate; adjudicated per statement by REV-01.
- **C3 — not trivial.** The statement ranges over more than one execution path.
  Classified by band:

| Band | Ranges over | In scope |
|------|-------------|----------|
| Evaluation | a closed term equals a literal | no — support only |
| Single path | one function, one branch | no — support only |
| Whole structure | an entire encoding or data structure: roundtrip, injectivity, canonicity | **yes** |
| Multi-site invariant | every call site that reaches a point | **yes** |
| Refinement | the code's state machine against the spec's | **yes** |
| Trace / cross-party | runs across epochs, and both parties | **yes** |

Rows in the two excluded bands are **support lemmas**, not deliverables: they
get proved when a target needs them, and they are never a phase goal. They are
not out of scope — they are out of the goal.

## Requirements

### Validated

<!-- Existing state of Spqr/Specs on main at d47083c, as recorded in the catalog. -->

- ✓ Aeneas extracts the whole crate including `lib.rs` `initial_state`, `send`, `recv` — existing
- ✓ Specs are written in WP style over the `Result` monad (`f args ⦃ r => P r ⦄`) — existing
- ✓ Proved on main: PROP-9, PROP-12a, PROP-15, PROP-17, PROP-18, PROP-31, PROP-36, PROP-40, PROP-42, LEAN-ENC-1, LEAN-GF; `generate_spec` (part of PROP-3); `hkdf_to_vec_spec`; `Message.serialize_spec`/`deserialize_spec` (components of PROP-35); label constants of PROP-41 — existing
- ✓ `hkdf_to_slice_spec` is the only hand-written axiom on main; the other opaque items are libcrux/prost stubs in `SrcTranslated/FunsExternal.lean` — existing
- ✓ Property IDs are stable — existing

### Active

<!-- Scope chosen 2026-09-15: the 18 non-trivial targets, plus the provenance and
     statement-review discipline that qualifies them. -->

- [ ] Every catalog row carries a `Source:` citation that resolves — ML-KEM Braid §, SCKA Def./Fig., or `src/path.rs:lines` at `d47083c` — and the provenance gate fails on a citation that does not (PROV-01)
- [ ] No property's proof work begins without an ACCEPT statement review recorded against its cited source, ruling on C1, C2 and C3 (REV-01)
- [ ] The **whole-structure** targets are proved: PROP-35's roundtrip on its corrected domain, the two new wire-format rows (STRUCT-02a's non-injectivity witness and STRUCT-02b's canonicity on the canonical domain), PROP-37 against the state-validity invariant Phase 7 designs — with `into_pb` injectivity stated as its corollary rather than as a separate row, STRUCT-04 having been retired on 2026-09-15 — PROP-10; LEAN-ENC-2's axiom narrowed to `decoded_message` with the surrounding encoder and decoder specs proved; PROP-38 proved or explicitly conditional on the classified prost `sorry`s
- [ ] The **multi-site invariant** targets are proved: PROP-24 (both KDF_OK sites plus their equality), PROP-25 (`ek_matches_header` on all four paths reaching `Ct1Sent::recv_ek`)
- [ ] The **refinement** targets are proved: PROP-47 transitions 1–13, PROP-30's Equal rows, PROP-49, PROP-43
- [ ] The **trace** targets are proved: PROP-22, PROP-21's trace part, PROP-23, PROP-50, and PROP-1 conditional on the PROP-3 axiom
- [ ] The three branch liveness axioms (`PolyEncoder.next_chunk`, `KeysUnsampled.send_hdr_chunk`, `HeaderReceived.send_ct1_chunk`) are theorems, and the branch's `Send.lean`/`Recv.lean`/`send_key` theorems are on `main`
- [ ] The trusted base is exactly the documented opaque stubs, each stated minimally and justified in one place
- [ ] Deviations D1–D5 each have a recorded decision in §11, so the refinement and trace statements are against a decided behaviour rather than an assumed one
- [ ] The catalog's status column and index are updated in the same PR as each theorem

### Out of Scope

- **Automated GitHub issue creation** — dropped 2026-09-15. Issues are not the unit of work; the PR is. No issue tooling, no per-property issue requirement
- Cryptographic security proofs (IND-CCA, SCKA security game) — the catalog covers functional correctness only; security is the SCKA paper's job
- Proving libcrux internals (`encapsulate1/2`, `decapsulate_compressed_key`, `validate_pk_bytes`, `hmac`) — opaque by design; they stay axioms
- Epoch wraparound at `u64::MAX` (§3.8) — excluded by `hax_lib::assume!` in the code; stated as an assumption
- SIMD `mul2_u16` dispatch — the unaccelerated GF(2^16) path is the verified one
- Evaluation-band and single-path-band rows as *deliverables* — they are support lemmas (see Target Selection)
- Changing `src/` for reasons other than a D1–D5 decision — code changes need Signal's agreement
- Outward-facing correspondence with Signal (the five-question deviation note) — deferred; the §11 decisions are recorded provisionally instead

## Context

- Repository: `SparsePostQuantumRatchet-verify`, branch `la/spec-catalog`, based on `main` at `d47083c`. All line numbers in the catalog refer to that commit.
- Toolchain: Rust crate under `src/`, extracted to Lean by Aeneas into `SrcTranslated/`; hand-written specs and proofs in `Spqr/Specs/` (209 `.lean` files). Proofs use `@[step]`-style lemmas and `mvcgen`.
- Sources for PROV-01: ML-KEM Braid Rev. 1 (`mlkembraid.pdf`, last updated 2025-09-26); SCKA — Auerbach, Dodis, Jost, Katsumata, Schmidt, *How to Compare Bandwidth Constrained Two-Party Secure Messaging Protocols* (`2025-2267.pdf`), Def. 3.1 and Fig. 1–2; the code at `d47083c`.
- Existing proof pattern: PRs #537–#541 each specify and verify one function in one file. The grain stays; the unit of delivery is one property per draft PR.
- The proofs branch `la/lean-v1-protocol-proofs` adds six files (862 lines): `Chain/{AddEpoch,Key,SendKey}.lean`, `States/{Send,Recv}.lean`, and `Specs/External.lean` holding liveness axioms. `Chain/AddEpoch.lean` and `Chain/Key.lean` overlap with theorems that have since landed on main under different paths; merging needs deduplication.
- `sorry-manifest.txt` (gitignored, generated) lists every declaration depending on a `sorry`. Most transitive entries trace to `MapCollectBridge` (aeneas#1043) and to prost `Message` impls.
- **Known catalog gap, found 2026-09-15**: every roundtrip row (PROP-35, PROP-37, PROP-38, LEAN-ENC-1) is stated only in the `decode(encode(x)) = x` direction. The converse is not stated anywhere, and for the wire format it appears to be **false** — `Spqr/Specs/V1/Chunked/States/Serialize/DecodeVarint.lean:43` records that `decode_varint` admits non-canonical LEB128 (`1` as `0x81 0x00`), so `deserialize` is not injective. Whether that is exploitable depends on what is MAC'd versus what is parsed, which has not been checked. **Ruled 2026-09-15**: this becomes **two** rows, not one — STRUCT-02a states the non-injectivity by explicit witness (the varint padding above, the ten-byte `% 2^64` truncation at `DecodeVarint.lean:44`, and `Ct1Ack(false)`/`Ct1Ack(true)` serialising identically because `serialize.rs:267` always rebuilds `true`), and STRUCT-02b proves injectivity on the canonical domain. The same pass found the roundtrip rows themselves are mis-stated: PROP-35's unrestricted `decode(encode(x)) = x` is **false** for epoch 0 and for `Ct1Ack(false)`, and PROP-37's is false without `pts_needed.val ≤ U32.max` (`polynomial.rs:795` narrows with `as u32`); both rows gain their domain in the PR that proves them. `States` protobuf injectivity is **not** a separate row — it is a one-line corollary of PROP-37's roundtrip, so the retired STRUCT-04's obligations fold into STRUCT-03.
- **Known plan-text error, found 2026-09-15**: the old MSG-01 wording ("PROP-35 proved from the existing component specs") understates the work. `deserialize_spec` is relational — existentials over varint block lengths with `varintBlockAt`/`chunkBlockAt` — not the inverse of `serialize_spec`. The composition needs a lemma connecting `varintBytes` to `varintBlockAt`, and no such lemma exists.
- Untracked local drafts in `docs/` (`props-draft-review.md`, `probe-lean-sorry-unsoundness.md`, `audit-prf-prng-acd19-4.3.md`, `report-consistency-check.md`) are working notes, not project inputs.
- Local `la/spec-catalog` is **ahead of** `origin/la/spec-catalog` by nine commits and zero behind as of 2026-09-14; a plain push suffices. Re-measure before pushing.

## Constraints

- **Trusted base**: no new hand-written axiom without a catalog entry explaining why it cannot be a theorem — the Core Value depends on this
- **Provenance**: every catalog row carries a resolvable `Source:` citation (PROV-01); theorem statements must match the catalog wording, and if a statement must change, the catalog changes in the same PR
- **Statement review**: no proof work on an unreviewed statement (REV-01). The review is cross-engine, read-only, and sees the statement plus its cited source; it rules on C1, C2 and C3 and is recorded before the proof exists
- **Process**: one draft PR per property, opened by the user. When a property's work is complete and verified, GSD stops and reports; the user creates the PR, then work continues with the next property. No GitHub issues
- **Review gates**: after `/gsd-plan-phase N` and before `/gsd-execute-phase N`, run `/spqr-plan-review N` (Codex, read-only, rubric `docs/rubrics/spqr-plan-review.md`); only APPROVE, or APPROVE-WITH-EDITS with all edits triaged and applied, routes to execution. After execution, alongside gsd-verifier, dispatch the `spqr-eval` agent on the phase diff; persist as `NN-EVAL.md`; FOLLOWUP routes to a gap-closure plan, HUMAN_RULING stops for the user
- **Gates**: the real checks are `lake build` with no non-sorry warning, `lake exe runLinter Spqr`, `lake env lean scripts/Audit.lean`, `#print axioms`, and the provenance check. `#check_no_sorry` in `docs/ISSUE_TEMPLATE.md` does not exist in the repo and must be removed
- **Tooling**: proofs must build with the repository's pinned Lean/Aeneas versions; no toolchain bumps inside a property PR
- **Code freeze**: `src/` changes are limited to D1–D5 resolutions agreed with Signal
- **Dependencies**: PROP-1 needs PROP-3 (axiom) and PROP-24; PROP-23 and PROP-50 need the per-transition results of PROP-47; PROP-38 and PROP-37 depend on prost `sorry`s and may end as trusted rather than proved; PROP-35's roundtrip needs a varint encoder/decoder agreement lemma that does not yet exist

## Key Decisions

| Decision | Rationale | Outcome |
|----------|-----------|---------|
| Goal is "prove as many non-trivial specs as possible", not "close every Open row" | User direction 2026-09-15; closing evaluation-band rows does not advance the verification argument | — Pending |
| C3 triviality measured by what the statement ranges over, not by expected proof effort | Cheap-given-lemmas is not the same as trivial; the first classification wrongly called roundtrips trivial on that confusion | — Pending |
| Roundtrips are in scope, and their converse direction becomes new catalog rows | Every roundtrip row states only the easy direction; canonicity is the malleability-relevant statement and is absent | — Pending |
| Every spec carries a resolvable source citation, gate-checked | User direction 2026-09-15 (C2); a property with no source cannot be distinguished from an invented one | — Pending |
| Statement review before proof, cross-engine, recorded | User direction 2026-09-15; a wrong statement wastes the proof, and the reviewer must not be the engine that wrote it | — Pending |
| Automated issue creation dropped | User direction 2026-09-15; the PR is the unit of work | — Pending |
| D1–D5 decisions recorded provisionally; Signal note deferred | The decisions fix which behaviour the refinement and trace theorems state; the correspondence does not | — Pending |
| Skip `/gsd-map-codebase` and GSD domain research | The catalog already grounds each property in code and Lean locations | — Pending |
| Order phases by dependency, not by spec section | Leaf lemmas unblock transitions, which unblock trace properties | — Pending |
| Interactive mode, standard granularity | A wrong lemma statement costs hours; confirm before each phase executes | — Pending |
| User opens all PRs; GSD stops at the PR boundary | User request 2026-09-14 | — Pending |

## Evolution

This document evolves at phase transitions and milestone boundaries.

**After each phase transition** (via `/gsd-transition`):
1. Requirements invalidated? → Move to Out of Scope with reason
2. Requirements validated? → Move to Validated with phase reference
3. New requirements emerged? → Add to Active
4. Decisions to log? → Add to Key Decisions
5. "What This Is" still accurate? → Update if drifted

**After each milestone** (via `/gsd-complete-milestone`):
1. Full review of all sections
2. Core Value check — still the right priority?
3. Audit Out of Scope — reasons still valid?
4. Update Context with current state

---
*Last updated: 2026-09-15 after the goal re-scope (prove non-trivial specs; provenance and statement review)*
