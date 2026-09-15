# Requirements: SPQR Property Proofs

**Defined:** 2026-09-14. **Re-scoped:** 2026-09-15.
**Core Value:** A proved property has a `sorry`-free Lean theorem, a resolvable source
citation, and a recorded ACCEPT statement review that preceded the proof.

"Proved" everywhere below means all of: theorem exists under `Spqr/Specs/`, module
re-exported from `Spqr.lean`, `lake build` clean of non-sorry warnings, `lake exe runLinter
Spqr` clean, `#print axioms` lists only builtin axioms and documented stubs, no new line in
`sorry-manifest.txt`, the row's `Source:` citation resolves, an ACCEPT review is on record
from before the proof, and the catalog row and §12 index updated in the same PR.

Requirements are grouped by the band of the statement (see `PROJECT.md` § Target Selection).
Bands **Evaluation** and **Single path** carry no requirements: those rows are support
lemmas, proved when a target needs them and named in that target's requirement.

## v1 Requirements

### Discipline (PROV, REV)

- [ ] **PROV-01**: Every row in `docs/spqr-properties.md` carries a `Source:` field citing **at least one** of ML-KEM Braid Rev. 1 §x.y, SCKA Def./Fig. n, or `src/path.rs:lines` at `d47083c`, semicolon-separated when a row has more than one ground (a spec section *and* the code implementing it); a provenance gate resolves **every** listed citation (file exists, line range within the file, spec section exists) and fails on any that does not. Pointers that are not one of the three source classes — a `Spqr/Specs/**` lemma, a planning doc — go on a separate `Evidence:` line, which carries no citation grammar and is outside the gate. Ruled 2026-09-15: the earlier "exactly one" wording would have forced a row with both a spec and a code ground to discard one, weakening the C2 traceability the field exists for
- [ ] **REV-01**: A statement review process exists and is binding: before any property's proof work, an independent cross-engine read-only reviewer receives the proposed Lean statement plus only its cited source and returns ACCEPT / REVISE / REJECT against C1 (not already proved), C2 (not invented — the statement says what the source says) and C3 (band). Verdicts are recorded per property in a tracked log; a property with no ACCEPT does not enter proof work; disputes stop for the user

### Infrastructure (INFRA)

- [ ] **INFRA-01**: No operative document (`docs/ISSUE_TEMPLATE.md`, `docs/rubrics/spqr-plan-review.md`, `CLAUDE.md`) cites a gate that does not exist in this repository; `docs/ISSUE_TEMPLATE.md` becomes a per-property **PR** checklist naming the five real gates plus the catalog-and-index update line
- [ ] **INFRA-03**: One repeatable local check runs all five gates (`lake build` non-sorry warnings, `runLinter Spqr`, `Audit.lean` sorry delta, `#print axioms` allowlist, provenance) and reports a per-gate verdict; its result on `main` matches CI's for the gates CI runs

### Merge and axiom removal (MERGE)

- [ ] **MERGE-01**: The per-variant `send` theorems of `la/lean-v1-protocol-proofs` `States/Send.lean` (PROP-21 send half) are on `main`
- [ ] **MERGE-02**: The `recv` Less and Greater theorems of `States/Recv.lean` (PROP-30 rows `msg.epoch < epoch` and `msg.epoch > epoch`, including the Ct2Sampled `epoch + 1` case) are on `main`
- [ ] **MERGE-03**: PROP-14 (`send_key` with `epoch < send_epoch` returns `SendKeyEpochDecreased`) is on `main`
- [ ] **MERGE-04**: The liveness axiom on `PolyEncoder.next_chunk` is replaced by a theorem stating when it succeeds
- [ ] **MERGE-05**: The liveness axiom on `KeysUnsampled.send_hdr_chunk` is replaced by a theorem
- [ ] **MERGE-06**: The liveness axiom on `HeaderReceived.send_ct1_chunk` is replaced by a theorem
- [ ] **MERGE-07**: The branch's `Chain/AddEpoch.lean` and `Chain/Key.lean` are reconciled with the `main` versions with no duplicate theorem names, and `VecDeque.push_back_spec` is either taken from the Aeneas standard library or proved

### Whole structure (STRUCT)

- [ ] **STRUCT-01**: PROP-35 — `Message.deserialize (Message.serialize m i) = ok (m, i, _)` **on the domain the code actually round-trips**: `0 < m.epoch` and, for a `Ct1Ack` payload, the Boolean is `true`. The unrestricted statement in the catalog is false — `serialize` discards `Ct1Ack`'s Boolean and epoch 0 is rejected — and the merged `Message.deserialize_spec` already carries both hypotheses (`Spqr/Specs/V1/Chunked/States/Serialize/Message/Deserialize.lean:65-77`), so the catalog row is behind the code and is corrected in the same PR (ruled 2026-09-15). Requires a new agreement lemma connecting the encoder model to the decoder predicate (`varintBytes v` satisfies `varintBlockAt` at the offset it occupies, and likewise `chunkBlockAt`), plus the `at1` length accounting. Support: PROP-36
- [ ] **STRUCT-02a**: **New row** — wire-format non-injectivity, stated as explicit witnesses. `deserialize` is not injective on byte strings and `serialize` is not injective on messages, and the theorem exhibits both: two distinct byte strings decoding to the same `(message, index)` (non-minimal LEB128, `1` as `0x81 0x00`, `DecodeVarint.lean:43`), and two distinct messages with identical serialization (`Ct1Ack(false)` and `Ct1Ack(true)`, because `serialize` drops the Boolean and `serialize.rs:267` always rebuilds `Ct1Ack(true)`). A negative result is the result. Code-grounded (§2.3 leaves the encoding to the implementer). Reviewed under REV-01 before proof
- [ ] **STRUCT-02b**: **New row** — wire-format canonicity on the canonical domain. `deserialize` *is* injective when restricted to canonical encodings: minimal varints, no trailing bytes, in the image of `serialize`. Shares STRUCT-01's `varintBytes`-to-`varintBlockAt` agreement lemma, which is why the two run in the same phase. Reviewed under REV-01 before proof
- [ ] **STRUCT-03**: PROP-37 — `States::from_pb (States::into_pb s) = ok s` for all eleven variants, including the chunked states whose per-state specs do not yet exist, **on a state-validity domain that Phase 7 designs and states**. The unrestricted row is **false**, and two independent reasons are on record: `src/encoding/polynomial.rs:795` narrows `pts_needed` with `as u32`, so the merged `into_pb_spec` needs `h_cast : pts_needed.val ≤ U32.max` (`Spqr/Specs/Encoding/Polynomial/PolyDecoder/IntoPb.lean:289`); and the unchunked deserializers gate on stored byte-vector lengths — `src/v1/unchunked/send_ct/serialize.rs:84` requires `es.len() == 2080`, `ct1.len() == 960`, `ek.len() == 1152` — while `into_pb` copies those vectors verbatim (`:75-81`), so a `Ct1SentEkReceived` with empty vectors serializes successfully and fails to deserialize, with no `PolyDecoder` and no prost `sorry` involved. **Ruled 2026-09-15**: representability alone was proposed and is *not sufficient*; the full invariant is not designed in Phase 1. Phase 1 annotates the row as known-false with the counterexample and leaves the statement alone (DEV/CAT finding, not a restatement); Phase 7 designs the invariant — field lengths as each deserializer requires, the variant-specific decoder-size checks such as `src/v1/chunked/send_ct/serialize.rs:18`, and representability — states the row against it, and proves it. The failure mode the proof must exclude is cross-variant confusion. Injectivity of `into_pb` on that domain follows as a corollary and is stated with the theorem (absorbed STRUCT-04)
- [x] ~~**STRUCT-04**~~: **Retired 2026-09-15, not dropped.** `States` protobuf injectivity is a one-line corollary of STRUCT-03, not independent content: on a domain where the roundtrip holds, `into_pb` succeeds, so from `into_pb s₁ = into_pb s₂ = ok p` and `from_pb p = ok sᵢ` for both, `s₁ = s₂`. The composition is **monadic** — `States.into_pb` returns `Result V1State` (`SrcTranslated/Funs.lean:10723`) — so the corollary is about equality of *successful* encodings, and it inherits whatever state-validity domain Phase 7 gives STRUCT-03 — which is why it could not be stated in Phase 1 either. As a separate target it failed C3 (it ranges over nothing STRUCT-03 does not) and came close to failing C1. Its two obligations move into STRUCT-03: state the corollary alongside the roundtrip, and state the counterexample family off the domain — two states whose `pts_needed` differ by `2^32` share an encoding, with no prost `sorry` involved. The genuinely unstated protobuf direction is canonicity (`into_pb (from_pb p) = p`), which sits behind the prost `sorry`s and is covered by STRUCT-07's conditionality rather than promoted to a target
- [ ] **STRUCT-05**: LEAN-ENC-2 — the axiom is narrowed to mention only `PolyDecoder.decoded_message`, and the surrounding encoder and decoder specs are theorems. Any `N` distinct codewords reconstruct the message (§3.6)
- [ ] **STRUCT-06**: PROP-10 — when `send_key` moves `send_epoch` forward it pops links older than `EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH = 1`, clears the send seed of every earlier link, leaves receive seeds untouched, and `KeyHistory` entries are removed on `get` or trimmed by `gc`. Support: PROP-12a, PROP-12b, PROP-29
- [ ] **STRUCT-07**: PROP-38 — `Chain::from_pb (c.into_pb ()) = ok c`, proved, or stated as explicitly conditional on the prost `Message` `sorry`s named in the AXIOM-05 classification, with the catalog row recording which of the two it is

### Multi-site invariant (SITE)

- [ ] **SITE-01**: PROP-24 — both KDF_OK sites (`HeaderReceived::send_ct1`, `EkSentCt1Received::recv_ct2`) call HKDF with salt `0^32`, IKM `ss`, info `"Signal_PQCKA_V1_MLKEM768:SCKA Key" ‖ epoch_be`, length 32, and the two derivations are equal for equal `ss` and epoch. Support: PROP-18, PROP-41 KDF_OK literal
- [ ] **SITE-02**: PROP-25 — on every `ek_decoder` completion (all four state/chunk combinations reaching `Ct1Sent::recv_ek`) `ek_matches_header(ek, hdr)` is checked before `ek` is used, and failure returns `ErroneousDataReceived`. Support: AXIOM-02 (PROP-3b)

### Refinement (REFINE)

- [ ] **REFINE-01**: PROP-47 side A — transitions 1–5 (`KeysUnsampled.send`, `KeysSampled.recv Ct1`, `HeaderSent.recv Ct1`, `Ct1Received.recv Ct2`, `EkSentCt1Received.recv Ct2`) each have a theorem giving the spec's effect on epoch, authenticator and payload, matching the D3 decision on `Ct1Ack(true)` emission. Support: PROP-45, PROP-48
- [ ] **REFINE-02**: PROP-47 side B — transitions 6–13 (`NoHeaderReceived.recv Hdr` through `Ct2Sampled.recv epoch + 1`) likewise, matching the D3 and D4 acceptance decisions
- [ ] **REFINE-03**: PROP-30 Equal rows — for `msg.epoch == epoch`, an unexpected payload type leaves the state unchanged with `key = None`, and the expected type takes the transition
- [ ] **REFINE-04**: PROP-49 — the emitted `EpochSecret.epoch` is `state.epoch` in transition 7 and the pre-increment epoch in transition 5, while the new state carries `epoch + 1`
- [ ] **REFINE-05**: PROP-43 — a failed `verify_hdr` in transition 6 and a failed `verify_ct` in transition 5 make `States::recv` return `Err`, and `lib.rs` `recv` stores no new state on `Err`, against the D5 caller contract. Support: PROP-15, PROP-31, PROP-40

### Trace and cross-party (TRACE)

- [ ] **TRACE-01**: PROP-22 — for every `States` variant, `send` puts `state.epoch()` in `msg.epoch` and leaves the epoch unchanged, so `t_snd = t_rcv = msg.epoch - 1`
- [ ] **TRACE-02**: PROP-21 trace part — a party never re-enters `HeaderReceived` or `EkSentCt1Received` at the same epoch, so at most one key is emitted per epoch. Also the recv half: every `recv` arm other than `EkSentCt1Received` on a completing `Ct2` returns `key = None`
- [ ] **TRACE-03**: PROP-23 — a party at state epoch `e` has emitted keys for epochs `1..e-1`, and `chain.add_epoch` was called with each. Support: PROP-9
- [ ] **TRACE-04**: PROP-50 — from `(KeysUnsampled_A(e), NoHeaderReceived_B(e))`, in-order delivery of every message reaches `(NoHeaderReceived_A(e+1), KeysUnsampled_B(e+1))`, and every reachable pair has a next step, for the D2-decided behaviour
- [ ] **TRACE-05**: PROP-1 — both parties' `EpochSecret.secret` for epoch `t` equal `KDF_OK(ss, t)` for the same `ss`, conditional on the PROP-3 KEM roundtrip axiom and nothing else hand-written

### Trusted base (AXIOM)

- [ ] **AXIOM-01**: PROP-3 is stated as a single axiom binding `hdr`, `ek`, `dk` to one `generate` call, quantified only over the libcrux stubs, with component sizes derived from `generate_spec`
- [ ] **AXIOM-02**: PROP-3b is stated as an axiom about `validate_pk_bytes` whose hashed byte string is taken from libcrux's FIPS 203 encoding, not from spec prose
- [ ] **AXIOM-04**: The two hand-written `sorry`s on `main` (`MapCollectBridge.lean:70`, `DecodeState.lean:54`) are each either discharged or listed in §1 as trusted with a reason and an upstream reference
- [ ] **AXIOM-05**: The prost `Message` `sorry`s are classified: which catalog properties depend on them transitively (from `sorry-manifest.txt`) and what a replacement model would need, recorded in §1
- [ ] **AXIOM-06**: `potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275` is either extracted (by removing the `cfg(not(hax))` log call from the extraction path) or its axiom stub documents the exact behaviour assumed

### Deviations (DEV)

- [ ] **DEV-01**: D1 (KDF_AUTH salt/IKM) has a recorded §11 decision and PROP-42's statement matches it
- [ ] **DEV-02**: D2 (future-epoch message is `Err`) has a recorded decision, and PROP-30 and PROP-50 are stated for the decided behaviour
- [ ] **DEV-03**: D3 and D4 (`Ct1Ack(true)` emission, extra accepted chunk types) have recorded decisions, and PROP-47's transition table matches them
- [ ] **DEV-04**: D5 (MAC failure does not abort the session) has a written caller contract under PROP-43 in §7, and PROP-43 is stated against it

### Catalog sync (CAT)

- [ ] **CAT-01**: Every theorem PR updates the property's status, its section text and the §12 index in `docs/spqr-properties.md`, so the catalog never lags `main`
- [ ] **CAT-02**: At the end of the milestone the index and the `Proved (branch)` status value are regenerated against `main`; the branch status value is removed once nothing uses it
- [ ] **CAT-03**: A ranked target list exists at `docs/proof-targets.md` recording, for every catalog row, its band, its C1/C2/C3 verdict, its source citation and its support-lemma dependencies — so the selection is auditable rather than implicit

## v2 Requirements

### Trusted base reduction

- **TB-01**: Replace the prost `Message` `sorry`s with a Lean model of protobuf encoding sufficient for PROP-37 and PROP-38 to become unconditional
- **TB-02**: Resolve aeneas#1043 upstream so `MapCollectBridge.lean:70` needs no `sorry`
- **TB-03**: Model `HMAC_SHA256` and `hkdf_to_slice` from a Lean SHA-256 so `hkdf_to_slice_spec` becomes a theorem

### Deferred from v1

- **DEV-05**: The outward-facing five-question deviation note to Signal, and the resulting rulings replacing the provisional §11 decisions
- **SEC-01**: Whether the wire-format non-canonicity of STRUCT-02a is exploitable — what is MAC'd versus what is parsed. Not checked; a security question, not a functional one

## Out of Scope

| Feature | Reason |
|---------|--------|
| Automated GitHub issue creation | Dropped 2026-09-15; the PR is the unit of work, not the issue |
| Evaluation-band and single-path-band rows as deliverables | Support lemmas, proved on demand; not phase goals (PROJECT.md § Target Selection) |
| Cryptographic security proofs (IND-CCA, SCKA game) | Functional correctness only; security is the SCKA paper's job |
| Proving libcrux internals | Opaque by design; they stay axioms |
| Epoch wraparound at `u64::MAX` (§3.8) | Excluded by `hax_lib::assume!`; stated as an assumption |
| SIMD `mul2_u16` dispatch | Unaccelerated GF(2^16) path is the verified one |
| `src/` changes outside D1–D5 | Code changes need Signal's agreement |
| Toolchain or Aeneas version bumps inside property PRs | Keeps each PR reviewable; bumps are separate work |

## Traceability

| Requirement | Band | Phase | Status |
|-------------|------|-------|--------|
| PROV-01 | discipline | Phase 1 | Pending |
| REV-01 | discipline | Phase 1 | Pending |
| INFRA-01 | infra | Phase 1 | Pending |
| INFRA-03 | infra | Phase 1 | Pending |
| CAT-03 | infra | Phase 1 | Pending |
| DEV-01 | deviation | Phase 1 | Pending |
| DEV-02 | deviation | Phase 1 | Pending |
| DEV-03 | deviation | Phase 1 | Pending |
| DEV-04 | deviation | Phase 1 | Pending |
| MERGE-01 | merge | Phase 2 | Pending |
| MERGE-02 | merge | Phase 2 | Pending |
| MERGE-03 | merge | Phase 2 | Pending |
| MERGE-04 | merge | Phase 2 | Pending |
| MERGE-05 | merge | Phase 2 | Pending |
| MERGE-06 | merge | Phase 2 | Pending |
| MERGE-07 | merge | Phase 2 | Pending |
| STRUCT-01 | whole structure | Phase 3 | Pending |
| STRUCT-02a | whole structure | Phase 3 | Pending |
| STRUCT-02b | whole structure | Phase 3 | Pending |
| STRUCT-05 | whole structure | Phase 3 | Pending |
| REFINE-01 | refinement | Phase 4 | Pending |
| REFINE-02 | refinement | Phase 4 | Pending |
| REFINE-03 | refinement | Phase 4 | Pending |
| REFINE-04 | refinement | Phase 4 | Pending |
| REFINE-05 | refinement | Phase 4 | Pending |
| SITE-02 | multi-site | Phase 4 | Pending |
| AXIOM-02 | trusted base | Phase 4 | Pending |
| TRACE-01 | trace | Phase 5 | Pending |
| TRACE-02 | trace | Phase 5 | Pending |
| TRACE-03 | trace | Phase 5 | Pending |
| TRACE-04 | trace | Phase 5 | Pending |
| SITE-01 | multi-site | Phase 6 | Pending |
| AXIOM-01 | trusted base | Phase 6 | Pending |
| TRACE-05 | trace | Phase 6 | Pending |
| STRUCT-03 | whole structure | Phase 7 | Pending |
| STRUCT-06 | whole structure | Phase 7 | Pending |
| STRUCT-07 | whole structure | Phase 7 | Pending |
| AXIOM-04 | trusted base | Phase 7 | Pending |
| AXIOM-05 | trusted base | Phase 7 | Pending |
| AXIOM-06 | trusted base | Phase 7 | Pending |
| CAT-01 | catalog | Phase 1 structurally, then all phases | Pending |
| CAT-02 | catalog | Phase 8 | Pending |

**Coverage:**
- v1 requirements: 42 total
- Mapped to phases: 42
- Unmapped: 0 ✓

Per-phase counts: Phase 1 = 9, Phase 2 = 7, Phase 3 = 4, Phase 4 = 7,
Phase 5 = 4, Phase 6 = 3, Phase 7 = 6, Phase 8 = 1, cross-phase = 1 (CAT-01).
Phase 3 gained STRUCT-02b and Phase 7 lost STRUCT-04 on 2026-09-15; the total is
unchanged.

Targets by band: whole structure 7, refinement 5, trace 5, multi-site 2,
axiom removal 3 (MERGE-04/05/06) = **22 proof targets**, of which 18 are
catalog rows and 4 are new or axiom-narrowing work.

A target is a **work unit, not a catalog row**, and the two do not correspond
one-to-one: MERGE-04/05/06 are axiom removals rather than rows, PROP-47 spans two
refinement requirements, and a partially proved row contributes only its **named open
obligation** (C1 in `PROJECT.md` — "partially proved rows qualify for their open
half"). `docs/proof-targets.md` records the obligation, not the row, as the unit, so
PROP-35 is a target on the strength of its open composed roundtrip even though its
component specs are proved. Ruled 2026-09-15.

The 2026-09-15 rulings left the count unchanged at 22 and whole structure unchanged at
7: STRUCT-02 split into STRUCT-02a and STRUCT-02b (+1), STRUCT-04 was retired into
STRUCT-03 as a corollary (−1).

---
*Requirements defined: 2026-09-14*
*Re-scoped: 2026-09-15 — goal is non-trivial specs with provenance and statement review; issue automation dropped*
