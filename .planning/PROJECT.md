# SPQR Property Proofs

## What This Is

A proof roadmap for the SPQR (Sparse Post-Quantum Ratchet) correctness
catalog in `docs/spqr-properties.md`. It takes every property whose status is
Open to a `sorry`-free Lean theorem on `main`, brings the theorems that exist
only on `la/lean-v1-protocol-proofs` onto `main`, reduces the trusted base to
the documented opaque stubs, and tracks the five spec-vs-code deviations as
decisions rather than proofs. The audience is the verification team working on
this repository and the Signal reviewers who read the catalog.

## Core Value

Every status in the catalog can be regenerated from the Lean sources on
`main`: a property marked Proved has a theorem with no `sorry` and no
hand-written axiom beyond the documented opaque stubs.

## Requirements

### Validated

<!-- Existing state of Spqr/Specs on main at d47083c, as recorded in the catalog. -->

- ✓ Aeneas extracts the whole crate including `lib.rs` `initial_state`, `send`, `recv` — existing
- ✓ Specs are written in WP style over the `Result` monad (`f args ⦃ r => P r ⦄`) — existing
- ✓ Proved on main: PROP-9, PROP-12a, PROP-15, PROP-17, PROP-18, PROP-31, PROP-36, PROP-40, PROP-42, LEAN-ENC-1, LEAN-GF; `generate_spec` (part of PROP-3); `hkdf_to_vec_spec`; `Message.serialize_spec`/`deserialize_spec` (components of PROP-35); label constants of PROP-41 — existing
- ✓ `hkdf_to_slice_spec` is the only hand-written axiom on main; the other opaque items are libcrux/prost stubs in `SrcTranslated/FunsExternal.lean` — existing
- ✓ Property IDs are stable and shared with the issue tracker; `docs/ISSUE_TEMPLATE.md` fixes the per-property issue shape — existing

### Active

<!-- Scope chosen 2026-09-14: Open properties, merge branch proofs, axiom hygiene, deviations D1-D5. -->

- [ ] Every Open property in the catalog has a theorem on `main` with `#check_no_sorry` passing: PROP-1, 10, 12b, 16, 22, 23, 24, 25, 27, 29, 37, 38, 43, 45, 47, 48, 49, 50, and the Open halves of PROP-21 (recv half, trace part), PROP-30 (Equal rows), PROP-35 (composed roundtrip), PROP-41 (KDF_OK literal)
- [ ] The Proved (branch) theorems (`Send.lean`, `Recv.lean` Less/Greater rows, `SendKey.lean` for PROP-14) are on `main`, with the three liveness axioms on defined functions (`PolyEncoder.next_chunk`, `KeysUnsampled.send_hdr_chunk`, `HeaderReceived.send_ct1_chunk`) replaced by theorems
- [ ] The remaining axioms (PROP-3, PROP-3b, LEAN-ENC-2, `hkdf_to_slice_spec`, `potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`) are stated minimally, bound to a single `generate` call where relevant, and each is justified in one place
- [ ] The two hand-written `sorry`s on main (`MapCollectBridge.lean:70`, `DecodeState.lean:54`) and the prost `Message` `sorry`s are either discharged or explicitly listed as trusted with a reason
- [ ] Deviations D1–D5 each have a recorded decision (code fix, spec erratum, or documented caller contract) and the affected property statements match the decision
- [ ] The catalog's status column and index are updated in the same PR as each theorem, so `docs/spqr-properties.md` never lags `main`

### Out of Scope

- Cryptographic security proofs (IND-CCA, SCKA security game) — the catalog covers functional correctness only; security is the SCKA paper's job
- Proving libcrux internals (`encapsulate1/2`, `decapsulate_compressed_key`, `validate_pk_bytes`, `hmac`) — opaque by design; they stay axioms
- Epoch wraparound at `u64::MAX` (§3.8) — excluded by `hax_lib::assume!` in the code; the catalog states it as an assumption, not a theorem
- SIMD `mul2_u16` dispatch — the unaccelerated GF(2^16) path is the verified one; the SIMD stub stays out
- Re-deriving the catalog itself — the property statements are fixed; this project proves them, it does not redesign them
- Changing `src/` for reasons other than a D1–D5 decision — code changes need Signal's agreement

## Context

- Repository: `SparsePostQuantumRatchet-verify`, branch `la/spec-catalog`, based on `main` at `d47083c`. All line numbers in the catalog refer to that commit.
- Toolchain: Rust crate under `src/`, extracted to Lean by Aeneas into `SrcTranslated/`; hand-written specs and proofs in `Spqr/Specs/` (209 `.lean` files). Proofs use `@[step]`-style lemmas and `mvcgen`.
- Existing proof pattern: recent PRs #537–#541 each specify and verify one function in one file, with an issue per property. The roadmap should keep that grain.
- The proofs branch `la/lean-v1-protocol-proofs` adds six files (862 lines): `Chain/{AddEpoch,Key,SendKey}.lean`, `States/{Send,Recv}.lean`, and `Specs/External.lean` holding liveness axioms. `Chain/AddEpoch.lean` and `Chain/Key.lean` overlap with theorems that have since landed on main under different paths (`Chain/Chain/AddEpoch.lean`, `Chain/ChainEpochDirection/Key.lean`); merging needs deduplication.
- `sorry-manifest.txt` (gitignored, generated) lists every declaration that depends on a `sorry`, directly or transitively. Most transitive entries trace to `MapCollectBridge` (aeneas#1043) and to prost `Message` impls.
- Untracked local drafts in `docs/` (`props-draft-review.md`, `probe-lean-sorry-unsoundness.md`, `audit-prf-prng-acd19-4.3.md`, `report-consistency-check.md`) are working notes, not project inputs.
- Local `la/spec-catalog` was rebased onto `main` and has diverged from `origin/la/spec-catalog`; pushing requires `--force-with-lease`.

## Constraints

- **Trusted base**: no new hand-written axiom without a catalog entry explaining why it cannot be a theorem — the Core Value depends on this
- **Provenance**: theorem statements must match the catalog wording; if a statement must change, the catalog changes in the same PR
- **Process**: one GitHub issue per property (from `docs/ISSUE_TEMPLATE.md`), one draft PR per issue closing it, following the #537–#541 pattern
- **Tooling**: proofs must build with the repository's pinned Lean/Aeneas versions; no toolchain bumps inside a property PR
- **Code freeze**: `src/` changes are limited to D1–D5 resolutions agreed with Signal
- **Dependencies**: PROP-1 needs PROP-3 (axiom) and PROP-24; PROP-23 and PROP-50 need the per-transition results of PROP-47; PROP-38 and PROP-37 depend on prost `sorry`s and may end as trusted rather than proved

## Key Decisions

| Decision | Rationale | Outcome |
|----------|-----------|---------|
| Skip `/gsd:map-codebase` | The catalog already grounds each property in code and Lean locations | — Pending |
| Scope = Open properties + merge branch proofs + axiom hygiene + D1–D5 | User choice 2026-09-14; covers every non-Proved catalog row | — Pending |
| Order phases by dependency, not by spec section | Leaf lemmas (constants, KDF sites, initial state) unblock transitions, which unblock trace properties | — Pending |
| New theorems land on `main` via one draft PR per property | Matches the existing #537–#541 workflow and keeps the catalog in sync | — Pending |
| Interactive mode, standard granularity | A wrong lemma statement costs hours; confirm before each phase executes | — Pending |

## Evolution

This document evolves at phase transitions and milestone boundaries.

**After each phase transition** (via `/gsd-transition`):
1. Requirements invalidated? → Move to Out of Scope with reason
2. Requirements validated? → Move to Validated with phase reference
3. New requirements emerged? → Add to Active
4. Decisions to log? → Add to Key Decisions
5. "What This Is" still accurate? → Update if drifted

**After each milestone** (via `/gsd:complete-milestone`):
1. Full review of all sections
2. Core Value check — still the right priority?
3. Audit Out of Scope — reasons still valid?
4. Update Context with current state

---
*Last updated: 2026-09-14 after initialization*
