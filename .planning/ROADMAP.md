# Roadmap: SPQR Property Proofs

## Overview

The catalog in `docs/spqr-properties.md` is the contract: every row must be
regenerable from the Lean sources on `main`. The work runs in dependency tiers.
First the gates and the five spec-vs-code decisions, because every later theorem
statement and every later PR checklist depends on them. Then the proofs that
already exist on `la/lean-v1-protocol-proofs` come to `main` with their liveness
axioms turned into theorems, since the state-machine and trace work builds on
`Send.lean` and `Recv.lean`. Then the leaf lemmas (constants, KDF sites, wire
format, initial states) and the trusted-base cleanup, which together fix the
vocabulary the transition proofs quantify over. Then the 13 transition
refinements, then the trace properties that compose them, then the chain layer,
and finally a regeneration of the catalog index against `main` so no row lags.

Process shape, identical in every phase: one GitHub issue per property from
`docs/ISSUE_TEMPLATE.md`, one draft PR per issue, following #537–#541. GSD stops
at each property's PR boundary and reports; the user opens the PR. After
`/gsd:plan-phase N` and before `/gsd:execute-phase N`, `/spqr-plan-review N`
must return APPROVE (or APPROVE-WITH-EDITS with every edit triaged and applied).
After execution, the `spqr-eval` agent runs alongside gsd-verifier on the phase
diff and is persisted as `NN-EVAL.md`.

"Proved" in every success criterion below means the full gate set: theorem under
`Spqr/Specs/`, module reachable from `Spqr.lean`, `lake build` with no non-sorry
warning, `lake exe runLinter Spqr` clean, `#print axioms` listing only builtin
axioms and the documented stubs, no new line from
`lake env lean scripts/Audit.lean` in `sorry-manifest.txt`, and the catalog row
plus §12 index updated in the same PR (CAT-01).

## Phases

**Phase Numbering:**

- Integer phases (1, 2, 3): Planned milestone work
- Decimal phases (2.1, 2.2): Urgent insertions (marked with INSERTED)

Decimal phases appear between their surrounding integers in numeric order.

- [ ] **Phase 1: Gates, Issues and Deviation Decisions** - Fix the real gate checklist, open one issue per property, and settle D1–D5 so every later statement is written once
- [ ] **Phase 2: Merge Branch Proofs** - Land `Send.lean`/`Recv.lean`/`send_key` on `main` with the three liveness axioms replaced by theorems
- [ ] **Phase 3: Parameters, KDF, Wire Format and Initialization** - Prove the leaf rows the transition proofs quantify over: constants, decoder sizes, KDF_OK, roundtrip, initial states, version negotiation
- [ ] **Phase 4: Trusted Base** - State PROP-3, PROP-3b, LEAN-ENC-2 and the libcrux stub minimally, and resolve or classify every remaining `sorry`
- [ ] **Phase 5: State Machine Transitions** - Prove the 13-row transition table, the Equal dispatch rows, key epoch, ek integrity and MAC failure
- [ ] **Phase 6: Trace Properties** - Prove the SCKA interface properties that compose transitions across epochs, up to session key consistency
- [ ] **Phase 7: Chain Layer** - Prove the `chain.rs` rows outside the spec: epoch indexing, key history, erasure, protobuf roundtrips
- [ ] **Phase 8: Catalog Regeneration** - Regenerate the index against `main` and retire the `Proved (branch)` status value

## Phase Details

### Phase 1: Gates, Issues and Deviation Decisions

**Goal**: The per-property workflow is trustworthy and the five spec-vs-code deviations are decided, so no later theorem has to be restated
**Depends on**: Nothing (first phase)
**Requirements**: INFRA-01, INFRA-02, INFRA-03, CAT-01, DEV-01, DEV-02, DEV-03, DEV-04
**Success Criteria** (what must be TRUE):

  1. `docs/ISSUE_TEMPLATE.md` names the four real gates (`lake build`, `lake exe runLinter Spqr`, `lake env lean scripts/Audit.lean`, `#print axioms`) plus a catalog-and-index update line; `grep -rn check_no_sorry` over the repo returns nothing
  2. One repeatable local check (a script under `scripts/` or a documented command sequence in the template) runs all four gates and reports pass/fail, and its result on `main` matches CI's
  3. `gh issue list` shows one open issue per v1 property, created from the corrected template, and each phase below names the issue numbers it closes
  4. `docs/spqr-properties.md` §11 carries a recorded decision for each of D1–D5 (code fix, spec erratum, or written caller contract), and PROP-42's §5 statement matches the D1 decision
  5. The catalog text for PROP-30, PROP-50, PROP-47 and PROP-43 states the decided behaviour for D2, D3/D4 and D5, so phases 5–6 can quote it verbatim

**Plans**: 9 plans across 2 PR boundaries (PR A: infra; PR B: deviations)

Plans:
**Wave 1**

- [ ] 01-01-PLAN.md — correct the issue template checklist and remove the phantom gate token from the operative documents (wave 1, PR A)
- [ ] 01-02-PLAN.md — reword INFRA-01/INFRA-02 and Phase 1 criteria 1 and 3 (wave 1, PR A)
- [ ] 01-03-PLAN.md — author scripts/check-gates.sh, the axiom allowlist, the check-lint shim and the gates README section (wave 1, PR A)

**Wave 2** *(blocked on Wave 1 completion)*

- [ ] 01-04-PLAN.md — author scripts/create-property-issues.sh and its two TSV data files (wave 2, PR A)
- [ ] 01-05-PLAN.md — retire the legacy issues/ tooling and its .gitignore rule (wave 2, PR A)
- [ ] 01-06-PLAN.md — build, run all four gates, cross-check against CI and run the negative controls (wave 2, PR A)

**Wave 3** *(blocked on Wave 2 completion)*

- [ ] 01-07-PLAN.md — create labels, file the PR A issues, stop and report at the PR A boundary (wave 3, PR A)

**Wave 4** *(blocked on Wave 3 completion)*

- [ ] 01-08-PLAN.md — record the D1–D5 decisions in §11, restate PROP-42/30/47/50 and write the PROP-43 caller contract (wave 4, PR B)

**Wave 5** *(blocked on Wave 4 completion)*

- [ ] 01-09-PLAN.md — draft the Signal deviation note, file the DEV issues, stop and report at the PR B boundary (wave 5, PR B)

### Phase 2: Merge Branch Proofs

**Goal**: The theorems that exist only on `la/lean-v1-protocol-proofs` are on `main`, axiom-free, deduplicated, and available as lemmas to later phases
**Depends on**: Phase 1 (gates; DEV-02 fixes the Greater-row statement of PROP-30)
**Requirements**: MERGE-01, MERGE-02, MERGE-03, MERGE-04, MERGE-05, MERGE-06, MERGE-07
**Success Criteria** (what must be TRUE):

  1. `Spqr/Specs/States/Send.lean` (one theorem per variant, PROP-21 send half), `States/Recv.lean` (Less and Greater rows including Ct2Sampled at `epoch + 1`) and the `send_key` epoch-decrease theorem (PROP-14) exist on `main`
  2. No axiom in `Spqr/Specs/` mentions `PolyEncoder.next_chunk`, `KeysUnsampled.send_hdr_chunk` or `HeaderReceived.send_ct1_chunk`; each has a theorem stating the conditions under which it succeeds
  3. No theorem name is defined twice across `Chain/AddEpoch.lean` vs `Chain/Chain/AddEpoch.lean` and `Chain/Key.lean` vs `Chain/ChainEpochDirection/Key.lean`, and `VecDeque.push_back_spec` is either imported from the Aeneas standard library or proved
  4. `#print axioms` on the merged `send`/`recv`/`send_key` theorems lists only builtin axioms and the documented stubs, and `sorry-manifest.txt` gains no line
  5. Catalog rows PROP-14, PROP-21 (send half) and PROP-30 (Less/Greater) read Proved rather than Proved (branch)

**Plans**: TBD (expect one per requirement, 7 PR boundaries)

### Phase 3: Parameters, KDF, Wire Format and Initialization

**Goal**: The leaf rows are proved, so the transition and trace proofs can cite constants, KDF derivations, message roundtrips and initial states instead of re-deriving them
**Depends on**: Phase 1 (gates)
**Requirements**: PARAM-01, PARAM-02, PARAM-03, MSG-01, SM-01, INIT-01, INIT-02
**Success Criteria** (what must be TRUE):

  1. Theorems evaluate `HEADER_SIZE = 64`, `ENCAPSULATION_KEY_SIZE = 1152`, `CIPHERTEXT1_SIZE = 960`, `CIPHERTEXT2_SIZE = 128` (PROP-45), and every decoder construction site is proved to use the catalog size — header `HEADER_SIZE + MACSIZE`, ek `ENCAPSULATION_KEY_SIZE`, ct1 `CIPHERTEXT1_SIZE`, ct2 `CIPHERTEXT2_SIZE + MACSIZE` (PROP-48)
  2. Both KDF_OK sites (`HeaderReceived::send_ct1`, `EkSentCt1Received::recv_ct2`) have theorems fixing salt `0^32`, IKM `ss`, info `"Signal_PQCKA_V1_MLKEM768:SCKA Key" ‖ epoch_be` and length 32, plus a theorem that the two derivations are equal for equal `ss` and epoch (PROP-24), and the info literal closes PROP-41's KDF_OK row
  3. `Message.deserialize (Message.serialize m i) = ok (m, i, _)` is a theorem composed from the existing `serialize_spec`/`deserialize_spec` (PROP-35)
  4. `initial_state` has theorems for A2B (`KeysUnsampled { epoch 1, Authenticator::new(k, 1) }`) and B2A (`NoHeaderReceived { epoch 1, Authenticator::new(k, 1), header_decoder }`), and `recv` has theorems for `MinimumVersion` and `VersionMismatch`
  5. Catalog rows PROP-45, PROP-24, PROP-41, PROP-35, PROP-48, PROP-27, PROP-16 read Proved, each with `#print axioms` clean and no new `sorry-manifest.txt` line

**Plans**: TBD (expect one per requirement, 7 PR boundaries)

### Phase 4: Trusted Base

**Goal**: The trusted base is exactly the documented opaque stubs, each stated minimally and justified in one place
**Depends on**: Phase 1 (gates), Phase 3 (`generate_spec`-derived sizes and the KDF site statements the axioms are bound against)
**Requirements**: AXIOM-01, AXIOM-02, AXIOM-03, AXIOM-04, AXIOM-05, AXIOM-06
**Success Criteria** (what must be TRUE):

  1. PROP-3 is a single axiom binding `hdr`, `ek`, `dk` to one `generate` call, quantified only over the libcrux stubs, with the component sizes derived from `generate_spec` rather than assumed
  2. The PROP-3b axiom's hashed byte string is taken from libcrux's FIPS 203 encoding with the source cited in the catalog, and the LEAN-ENC-2 axiom mentions only `PolyDecoder.decoded_message` while the surrounding encoder and decoder specs are theorems
  3. `MapCollectBridge.lean:70` and `DecodeState.lean:54` are each either discharged or listed in §1 as trusted with a reason and an upstream reference (aeneas#1043), and every remaining `sorry` in `Spqr/Specs/` appears in that §1 list
  4. §1 records, for each catalog property that depends on the prost `Message` `sorry`s, the transitive path from `sorry-manifest.txt` and what a replacement model would have to provide
  5. `potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275` is either extracted (the `cfg(not(hax))` log call removed from the extraction path) or its axiom stub documents the exact assumed behaviour

**Plans**: TBD (expect one per requirement, 6 PR boundaries)

### Phase 5: State Machine Transitions

**Goal**: Every spec transition, dispatch row and integrity check of §2.5 is a theorem about the code path the catalog names
**Depends on**: Phase 2 (`Send.lean`/`Recv.lean` as lemma base), Phase 3 (constants, KDF_OK, decoder sizes), Phase 4 (PROP-3b for the ek check), Phase 1 (D3/D4/D5 decisions)
**Requirements**: SM-02, SM-03, SM-04, SM-05, SM-06, SM-07, AUTH-01
**Success Criteria** (what must be TRUE):

  1. PROP-47 transitions 1–5 and 6–13 each have a named theorem giving the catalog's effect on epoch, authenticator and payload, and the statements match the D3 (`Ct1Ack(true)` emission, `Ct1Ack(true)` acceptance) and D4 (extra `Ek` acceptance) decisions from Phase 1
  2. PROP-30's Equal rows are theorems per variant: an unexpected payload type leaves the state unchanged with `key = None`, the expected type takes the transition
  3. PROP-49 is a theorem: the emitted `EpochSecret.epoch` is `state.epoch` in transition 7 and the pre-increment epoch in transition 5, while the new state carries `epoch + 1`
  4. PROP-25 is a theorem over all four state/chunk combinations reaching `Ct1Sent::recv_ek` (`ek_matches_header` checked before `ek` is used, failure returns `ErroneousDataReceived`), and PROP-21's recv half is a theorem: every `recv` arm other than `EkSentCt1Received` on a completing `Ct2` returns `key = None`
  5. PROP-43 is a theorem against the D5 caller contract: failed `verify_hdr` in transition 6 and failed `verify_ct` in transition 5 make `States::recv` return `Err`, and `lib.rs` `recv` stores no new state on `Err`

**Plans**: TBD (expect one per requirement, 7 PR boundaries)

### Phase 6: Trace Properties

**Goal**: The SCKA interface properties hold across epochs, up to session key consistency
**Depends on**: Phase 5 (per-transition results), Phase 3 (PROP-24), Phase 4 (PROP-3 axiom), Phase 1 (D2 decision)
**Requirements**: TRACE-01, TRACE-02, TRACE-03, TRACE-04, TRACE-05
**Success Criteria** (what must be TRUE):

  1. PROP-22 is a theorem for every `States` variant: `send` puts `state.epoch()` in `msg.epoch` and no `send` arm changes the epoch, so `t_snd = t_rcv = msg.epoch - 1`
  2. PROP-21's trace part is a theorem: a party never re-enters `HeaderReceived` or `EkSentCt1Received` at the same epoch, hence at most one key per epoch
  3. PROP-23 is a theorem: a party at state epoch `e` has emitted keys for epochs `1..e-1` and `chain.add_epoch` was called with each, composed with the proved `add_epoch_spec` (PROP-9)
  4. PROP-50 is a theorem for the D2-decided behaviour: from `(KeysUnsampled_A(e), NoHeaderReceived_B(e))`, in-order delivery of every message reaches `(NoHeaderReceived_A(e+1), KeysUnsampled_B(e+1))`, and every reachable pair has a next step
  5. PROP-1 is a theorem conditional on the PROP-3 KEM roundtrip axiom: both parties' `EpochSecret.secret` for epoch `t` equal `KDF_OK(ss, t)` for the same `ss`; `#print axioms` shows the PROP-3 axiom and no other hand-written one

**Plans**: TBD (expect one per requirement, 5 PR boundaries)

### Phase 7: Chain Layer

**Goal**: The `chain.rs` rows that sit outside the spec are proved, or explicitly conditional on a classified trusted item
**Depends on**: Phase 1 (gates), Phase 4 (AXIOM-05 prost classification for PROP-38)
**Requirements**: CHAIN-01, CHAIN-02, CHAIN-03, CHAIN-04, CHAIN-05
**Success Criteria** (what must be TRUE):

  1. PROP-29 is a theorem in both directions: `epoch_idx(e) = Ok(links.len() - 1 - (current_epoch - e))` iff `e ≤ current_epoch` and the difference is below `links.len()`, else `Err(EpochOutOfRange(e))`
  2. PROP-12b is a theorem: `get` after `add` of a fresh counter returns the stored 32-byte key and removes the entry
  3. PROP-10 is a theorem: advancing `send_epoch` pops links older than one epoch before `send_epoch`, clears the send seed of every earlier link, leaves receive seeds untouched, and `KeyHistory` entries are removed on `get` or trimmed by `gc`
  4. PROP-37 is a theorem for all eleven `States` variants (`States::from_pb (States::into_pb s) = ok s`), built on the existing per-state `into_pb`/`from_pb` specs
  5. PROP-38 is either a theorem or an explicitly conditional statement whose hypotheses are the prost `Message` `sorry`s named in the Phase 4 classification, with the catalog row recording which of the two it is

**Plans**: TBD (expect one per requirement, 5 PR boundaries)

### Phase 8: Catalog Regeneration

**Goal**: The catalog is a faithful rendering of `main`, with no status value left that nothing uses
**Depends on**: Phases 2–7 (every status the index reports)
**Requirements**: CAT-02
**Success Criteria** (what must be TRUE):

  1. The §12 index is regenerated against `main`, and every row's status is supported by a theorem, an axiom entry or a documented trusted item in §1
  2. `Proved (branch)` appears nowhere in `docs/spqr-properties.md` — neither in the status legend nor in any row — and the paragraph describing the branch liveness axioms is removed or rewritten as history
  3. A fresh run of the Phase 1 local gate check over `main` reproduces every Proved status, and `sorry-manifest.txt` contains only entries listed in §1

**Plans**: TBD (1 PR boundary)

## Progress

**Execution Order:**
Phases execute in numeric order: 1 → 2 → 3 → 4 → 5 → 6 → 7 → 8

| Phase | Plans Complete | Status | Completed |
|-------|----------------|--------|-----------|
| 1. Gates, Issues and Deviation Decisions | 0/9 | Not started | - |
| 2. Merge Branch Proofs | 0/TBD | Not started | - |
| 3. Parameters, KDF, Wire Format and Initialization | 0/TBD | Not started | - |
| 4. Trusted Base | 0/TBD | Not started | - |
| 5. State Machine Transitions | 0/TBD | Not started | - |
| 6. Trace Properties | 0/TBD | Not started | - |
| 7. Chain Layer | 0/TBD | Not started | - |
| 8. Catalog Regeneration | 0/TBD | Not started | - |

## Notes

- CAT-01 is assigned to Phase 1 because that is where the requirement is
  discharged structurally (the template gains the catalog-update line), but the
  rule applies to every PR in every phase: the property's status, its section
  text and the §12 index change in the same PR as the theorem.

- Phase 1's DEV requirements depend on input from Signal. If a decision is
  outstanding when a later phase needs it, the affected property is stated
  against the code as it is and the catalog records the statement as provisional
  on that deviation; re-stating it is then a new phase insertion, not a silent
  edit.

- CHAIN-05 (PROP-38) and TRACE-05 (PROP-1) are the two rows that may legitimately
  end as conditional theorems. Both must name their hypotheses in the catalog.
