# Requirements: SPQR Property Proofs

**Defined:** 2026-09-14
**Core Value:** Every status in `docs/spqr-properties.md` can be regenerated from the Lean sources on `main`: Proved means a theorem with no `sorry` and no hand-written axiom beyond the documented opaque stubs.

Each requirement names the catalog row it discharges. "Proved" everywhere below means: theorem
exists under `Spqr/Specs/`, module re-exported from `Spqr.lean`, `lake build` clean of non-sorry
warnings, `#print axioms` lists only builtin axioms and documented stubs, no new line in
`sorry-manifest.txt`, and the catalog row and index updated in the same PR.

## v1 Requirements

### Infrastructure (INFRA)

- [ ] **INFRA-01**: `docs/ISSUE_TEMPLATE.md` checklist names the real gates (`lake build`, `lake exe runLinter Spqr`, `lake env lean scripts/Audit.lean`, `#print axioms`) instead of the nonexistent `#check_no_sorry`
- [ ] **INFRA-02**: A GitHub issue exists for every property in v1 scope, created from the template, labelled by type and status, and referenced from the roadmap phase that proves it
- [ ] **INFRA-03**: A repeatable local check (script or documented command sequence) reproduces CI's build, lint and sorry-manifest gates so a property can be declared done before the PR is opened

### Merge branch proofs (MERGE)

- [ ] **MERGE-01**: The per-variant `send` theorems of `la/lean-v1-protocol-proofs` `States/Send.lean` (PROP-21 send half: only `HeaderReceived.send` returns a key) are on `main`
- [ ] **MERGE-02**: The `recv` Less and Greater theorems of `States/Recv.lean` (PROP-30 rows `msg.epoch < epoch` and `msg.epoch > epoch`, including the Ct2Sampled `epoch + 1` case) are on `main`
- [ ] **MERGE-03**: PROP-14 (`send_key` with `epoch < send_epoch` returns `SendKeyEpochDecreased`) is on `main`
- [ ] **MERGE-04**: The liveness axiom on `PolyEncoder.next_chunk` is replaced by a theorem stating when it succeeds
- [ ] **MERGE-05**: The liveness axiom on `KeysUnsampled.send_hdr_chunk` is replaced by a theorem
- [ ] **MERGE-06**: The liveness axiom on `HeaderReceived.send_ct1_chunk` is replaced by a theorem
- [ ] **MERGE-07**: The branch's `Chain/AddEpoch.lean` and `Chain/Key.lean` are reconciled with the `main` versions (`Chain/Chain/AddEpoch.lean`, `Chain/ChainEpochDirection/Key.lean`) with no duplicate theorem names, and `VecDeque.push_back_spec` is either taken from the Aeneas standard library or proved

### Parameters and KDF (PARAM)

- [ ] **PARAM-01**: PROP-45 — `HEADER_SIZE = 64`, `ENCAPSULATION_KEY_SIZE = 1152`, `CIPHERTEXT1_SIZE = 960`, `CIPHERTEXT2_SIZE = 128` are proved by evaluation of the extracted constants
- [ ] **PARAM-02**: PROP-24 — both KDF_OK sites (`HeaderReceived::send_ct1`, `EkSentCt1Received::recv_ct2`) are proved to call HKDF with salt `0^32`, IKM `ss`, info `"Signal_PQCKA_V1_MLKEM768:SCKA Key" ‖ epoch_be`, length 32, and the two derivations are proved equal for equal `ss` and epoch
- [ ] **PARAM-03**: PROP-41 — the KDF_OK info literal is covered by a theorem, closing the label-prefix property for all five labels

### Messages (MSG)

- [ ] **MSG-01**: PROP-35 — the composed roundtrip `Message.deserialize (Message.serialize m i) = ok (m, i, _)` is proved from the existing component specs

### Authenticator (AUTH)

- [ ] **AUTH-01**: PROP-43 — a failed `verify_hdr` in transition 6 and a failed `verify_ct` in transition 5 make `States::recv` return `Err`, and `lib.rs` `recv` is proved to store no new state on `Err`

### Initialization (INIT)

- [ ] **INIT-01**: PROP-27 — `initial_state` with A2B yields `KeysUnsampled { epoch 1, Authenticator::new(k, 1) }` and with B2A yields `NoHeaderReceived { epoch 1, Authenticator::new(k, 1), header_decoder }`
- [ ] **INIT-02**: PROP-16 — `recv` returns `MinimumVersion` when the peer version is below ours and below `min_version`, and `VersionMismatch` when below ours with no negotiation record

### State machine (SM)

- [ ] **SM-01**: PROP-48 — every decoder construction site uses the catalog's message size (header `HEADER_SIZE + MACSIZE`, ek `ENCAPSULATION_KEY_SIZE`, ct1 `CIPHERTEXT1_SIZE`, ct2 `CIPHERTEXT2_SIZE + MACSIZE`)
- [ ] **SM-02**: PROP-30 Equal rows — for `msg.epoch == epoch`, an unexpected payload type leaves the state unchanged with `key = None`, and the expected type takes the transition
- [ ] **SM-03**: PROP-47 side A — transitions 1–5 (`KeysUnsampled.send`, `KeysSampled.recv Ct1`, `HeaderSent.recv Ct1`, `Ct1Received.recv Ct2`, `EkSentCt1Received.recv Ct2`) are proved with the catalog's effect on epoch, authenticator and payload, including the D3 `Ct1Ack(true)` emission
- [ ] **SM-04**: PROP-47 side B — transitions 6–13 (`NoHeaderReceived.recv Hdr` through `Ct2Sampled.recv epoch + 1`) are proved with the catalog's effect on epoch, authenticator and payload, including D3 and D4 acceptance
- [ ] **SM-05**: PROP-49 — the emitted `EpochSecret.epoch` is `state.epoch` in transition 7 and the pre-increment epoch in transition 5 while the new state carries `epoch + 1`
- [ ] **SM-06**: PROP-25 — on every `ek_decoder` completion (four state/chunk combinations reaching `Ct1Sent::recv_ek`) `ek_matches_header(ek, hdr)` is checked before `ek` is used and failure returns `ErroneousDataReceived`
- [ ] **SM-07**: PROP-21 recv half — every `recv` arm other than `EkSentCt1Received` on a completing `Ct2` returns `key = None`

### Trace properties (TRACE)

- [ ] **TRACE-01**: PROP-22 — for every `States` variant, `send` puts `state.epoch()` in `msg.epoch` and leaves the epoch unchanged, so `t_snd = t_rcv = msg.epoch - 1`
- [ ] **TRACE-02**: PROP-21 trace part — a party never re-enters `HeaderReceived` or `EkSentCt1Received` at the same epoch, so at most one key is emitted per epoch
- [ ] **TRACE-03**: PROP-23 — a party at state epoch `e` has emitted keys for epochs `1..e-1`, and `chain.add_epoch` was called with each
- [ ] **TRACE-04**: PROP-50 — from `(KeysUnsampled_A(e), NoHeaderReceived_B(e))`, in-order delivery of every message reaches `(NoHeaderReceived_A(e+1), KeysUnsampled_B(e+1))`, and every reachable pair has a next step
- [ ] **TRACE-05**: PROP-1 — both parties' `EpochSecret.secret` for epoch `t` equal `KDF_OK(ss, t)` for the same `ss`, stated as a theorem conditional on the PROP-3 KEM roundtrip axiom

### Chain layer (CHAIN)

- [ ] **CHAIN-01**: PROP-29 — `epoch_idx(e)` returns `Ok(links.len() - 1 - (current_epoch - e))` iff `e ≤ current_epoch` and the difference is below `links.len()`, else `Err(EpochOutOfRange(e))`
- [ ] **CHAIN-02**: PROP-12b — `get` after `add` of a fresh counter returns the stored 32-byte key and removes the entry
- [ ] **CHAIN-03**: PROP-10 — when `send_key` advances `send_epoch` it pops links older than one epoch before `send_epoch`, clears the send seed of every earlier link, leaves receive seeds untouched, and `KeyHistory` entries are removed on `get` or trimmed by `gc`
- [ ] **CHAIN-04**: PROP-37 — `States::from_pb (States::into_pb s) = ok s` for all eleven variants, building on the existing per-state specs
- [ ] **CHAIN-05**: PROP-38 — `Chain::from_pb (c.into_pb ()) = ok c`, stated as a theorem conditional on the prost `Message` sorrys and recorded as such in the catalog if they cannot be discharged

### Axiom hygiene (AXIOM)

- [ ] **AXIOM-01**: PROP-3 is stated as a single axiom binding `hdr`, `ek`, `dk` to one `generate` call, quantified only over the libcrux stubs, with `generate_spec` used to derive the component sizes
- [ ] **AXIOM-02**: PROP-3b is stated as an axiom about `validate_pk_bytes` whose hashed byte string is taken from libcrux's FIPS 203 encoding, not from the spec prose
- [ ] **AXIOM-03**: LEAN-ENC-2 is stated as an axiom about `PolyDecoder.decoded_message` only, with the surrounding encoder/decoder specs proved
- [ ] **AXIOM-04**: The two hand-written sorrys on `main` (`MapCollectBridge.lean:70`, `DecodeState.lean:54`) are each either discharged or listed in the catalog as trusted with a reason and an upstream reference
- [ ] **AXIOM-05**: The prost `Message` sorrys are classified: which catalog properties depend on them transitively (from `sorry-manifest.txt`) and what a replacement model would need, recorded in the catalog's verification-setup section
- [ ] **AXIOM-06**: `potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275` is either extracted (by removing the `cfg(not(hax))` log call from the extraction path) or its axiom stub is documented with the exact behaviour assumed

### Deviations (DEV)

- [ ] **DEV-01**: D1 (KDF_AUTH salt/IKM) has a recorded decision from Signal: code fix or spec erratum, and PROP-42's statement matches it
- [ ] **DEV-02**: D2 (future-epoch message is `Err`) has a recorded decision, and PROP-30 and PROP-50 are stated for the decided behaviour
- [ ] **DEV-03**: D3 and D4 (`Ct1Ack(true)` emission, extra accepted chunk types) have recorded decisions, and PROP-47's transition table matches them
- [ ] **DEV-04**: D5 (MAC failure does not abort the session) has a written caller contract, and PROP-43 is stated against it

### Catalog sync (CAT)

- [ ] **CAT-01**: Every theorem PR updates the property's status, its section text and the index in `docs/spqr-properties.md`, so the catalog never lags `main`
- [ ] **CAT-02**: At the end of the milestone the catalog index and the `Proved (branch)` status value are regenerated against `main`; the branch status value is removed once nothing uses it

## v2 Requirements

### Trusted base reduction

- **TB-01**: Replace the prost `Message` sorrys with a Lean model of protobuf encoding sufficient for PROP-37 and PROP-38 to become unconditional
- **TB-02**: Resolve aeneas#1043 upstream so `MapCollectBridge.lean:70` needs no sorry
- **TB-03**: Model `HMAC_SHA256` and `hkdf_to_slice` from a Lean SHA-256 so `hkdf_to_slice_spec` becomes a theorem

## Out of Scope

| Feature | Reason |
|---------|--------|
| Cryptographic security proofs (IND-CCA, SCKA game) | Functional correctness only; security is the SCKA paper's job |
| Proving libcrux internals | Opaque by design; they stay axioms |
| Epoch wraparound at `u64::MAX` (§3.8) | Excluded by `hax_lib::assume!`; stated as an assumption |
| SIMD `mul2_u16` dispatch | Unaccelerated GF(2^16) path is the verified one |
| Redesigning catalog statements | Statements are fixed; a proof-forced rewording is a catalog fix, not a redesign |
| `src/` changes outside D1–D5 | Code changes need Signal's agreement |
| Toolchain or Aeneas version bumps inside property PRs | Keeps each PR reviewable; bumps are separate work |

## Traceability

Which phases cover which requirements. Updated during roadmap creation.

| Requirement | Phase | Status |
|-------------|-------|--------|
| INFRA-01 | Phase 1 | Pending |
| INFRA-02 | Phase 1 | Pending |
| INFRA-03 | Phase 1 | Pending |
| MERGE-01 | Phase 2 | Pending |
| MERGE-02 | Phase 2 | Pending |
| MERGE-03 | Phase 2 | Pending |
| MERGE-04 | Phase 2 | Pending |
| MERGE-05 | Phase 2 | Pending |
| MERGE-06 | Phase 2 | Pending |
| MERGE-07 | Phase 2 | Pending |
| PARAM-01 | Phase 3 | Pending |
| PARAM-02 | Phase 3 | Pending |
| PARAM-03 | Phase 3 | Pending |
| MSG-01 | Phase 3 | Pending |
| AUTH-01 | Phase 5 | Pending |
| INIT-01 | Phase 3 | Pending |
| INIT-02 | Phase 3 | Pending |
| SM-01 | Phase 3 | Pending |
| SM-02 | Phase 5 | Pending |
| SM-03 | Phase 5 | Pending |
| SM-04 | Phase 5 | Pending |
| SM-05 | Phase 5 | Pending |
| SM-06 | Phase 5 | Pending |
| SM-07 | Phase 5 | Pending |
| TRACE-01 | Phase 6 | Pending |
| TRACE-02 | Phase 6 | Pending |
| TRACE-03 | Phase 6 | Pending |
| TRACE-04 | Phase 6 | Pending |
| TRACE-05 | Phase 6 | Pending |
| CHAIN-01 | Phase 7 | Pending |
| CHAIN-02 | Phase 7 | Pending |
| CHAIN-03 | Phase 7 | Pending |
| CHAIN-04 | Phase 7 | Pending |
| CHAIN-05 | Phase 7 | Pending |
| AXIOM-01 | Phase 4 | Pending |
| AXIOM-02 | Phase 4 | Pending |
| AXIOM-03 | Phase 4 | Pending |
| AXIOM-04 | Phase 4 | Pending |
| AXIOM-05 | Phase 4 | Pending |
| AXIOM-06 | Phase 4 | Pending |
| DEV-01 | Phase 1 | Pending |
| DEV-02 | Phase 1 | Pending |
| DEV-03 | Phase 1 | Pending |
| DEV-04 | Phase 1 | Pending |
| CAT-01 | Phase 1 | Pending |
| CAT-02 | Phase 8 | Pending |

**Coverage:**
- v1 requirements: 46 total
- Mapped to phases: 46
- Unmapped: 0 ✓

Per-phase counts: Phase 1 = 8, Phase 2 = 7, Phase 3 = 7, Phase 4 = 6,
Phase 5 = 7, Phase 6 = 5, Phase 7 = 5, Phase 8 = 1.

---
*Requirements defined: 2026-09-14*
*Last updated: 2026-09-14 after roadmap creation (traceability filled)*
