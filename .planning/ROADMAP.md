# Roadmap: SPQR Property Proofs

## Overview

The goal is to prove as many **non-trivial** catalog specifications as possible.
Non-trivial is defined in `PROJECT.md` § Target Selection by what the statement
ranges over: whole structure, multi-site invariant, refinement, and trace /
cross-party statements are targets; evaluation-band and single-path-band rows are
support lemmas, proved when a target needs them and never a phase goal.

Two disciplines run across every phase. **PROV-01**: every catalog row carries a
`Source:` citation that resolves to ML-KEM Braid Rev. 1, the SCKA paper, or `src/`
at `d47083c`, gate-checked. **REV-01**: no property's proof begins before an
independent cross-engine review of its *statement* against its cited source
returns ACCEPT — because a wrong statement wastes the proof, not just the review.

The work runs in dependency tiers. Phase 1 builds the gates, retrofits provenance,
produces the reviewed target list, and records the five spec-vs-code decisions that
fix which behaviour the refinement and trace statements assert. Phase 2 brings the
existing branch proofs to `main` and turns their three liveness axioms into
theorems, because the refinement work builds on `Send.lean` and `Recv.lean`.
Phase 3 takes the encoding layer, which is independent of the state machine and can
run alongside Phase 2. Phase 4 proves the 13-row transition refinement and its
siblings. Phase 5 composes them into trace properties. Phase 6 reaches session key
consistency, the capstone. Phase 7 takes the chain layer and the protobuf
roundtrips, whose value depends on classifying the prost `sorry`s. Phase 8
regenerates the catalog against `main`.

Process shape, identical in every phase: one draft PR per property, following
#537–#541. There are no GitHub issues — the PR is the unit of work. GSD stops at
each property's PR boundary and reports; the user opens the PR. After
`/gsd-plan-phase N` and before `/gsd-execute-phase N`, `/spqr-plan-review N` must
return APPROVE (or APPROVE-WITH-EDITS with every edit triaged and applied). After
execution, the `spqr-eval` agent runs alongside gsd-verifier on the phase diff and
is persisted as `NN-EVAL.md`.

"Proved" in every success criterion below means the full gate set: theorem under
`Spqr/Specs/`, module reachable from `Spqr.lean`, `lake build` with no non-sorry
warning, `lake exe runLinter Spqr` clean, `#print axioms` listing only builtin
axioms and the documented stubs, no new line from `lake env lean scripts/Audit.lean`
in `sorry-manifest.txt`, the row's `Source:` citation resolving, an ACCEPT statement
review on record from before the proof, and the catalog row plus §12 index updated
in the same PR (CAT-01).

## Phases

**Phase Numbering:**

- Integer phases (1, 2, 3): Planned milestone work
- Decimal phases (2.1, 2.2): Urgent insertions (marked with INSERTED)

Decimal phases appear between their surrounding integers in numeric order.

- [ ] **Phase 1: Gates, Provenance and the Reviewed Target List** - Make "proved" checkable, make every row cite a resolvable source, make the statement review binding, and settle D1–D5
- [ ] **Phase 2: Merge and Axiom Removal** - Land `Send.lean`/`Recv.lean`/`send_key` on `main` with the three liveness axioms replaced by theorems
- [ ] **Phase 3: Encoding Layer — Roundtrips and Canonicity** - Prove the wire-format roundtrip, state and prove the canonicity direction the catalog omits, and narrow the erasure-code axiom
- [ ] **Phase 4: Transition Refinement** - Prove the 13-row transition table, the Equal dispatch rows, key epoch, ek integrity and MAC failure
- [ ] **Phase 5: Trace Properties** - Compose the per-transition results into epoch-agreement, one-key-per-epoch, epoch knowledge and structural liveness
- [ ] **Phase 6: Session Key Consistency** - Prove PROP-1 on a minimal PROP-3 axiom and the KDF_OK site equality
- [ ] **Phase 7: Chain Layer and Serialization** - Prove chain GC, classify the prost `sorry`s, and settle the protobuf roundtrips and their injectivity
- [ ] **Phase 8: Catalog Regeneration** - Regenerate the index against `main` and retire the `Proved (branch)` status value

## Phase Details

### Phase 1: Gates, Provenance and the Reviewed Target List

**Goal**: "Proved" is mechanically checkable, every catalog row cites a source that resolves, the statement review is binding and demonstrated, and D1–D5 are decided so no later statement has to be rewritten
**Depends on**: Nothing (first phase)
**Requirements**: INFRA-01, INFRA-03, PROV-01, REV-01, CAT-01, CAT-03, DEV-01, DEV-02, DEV-03, DEV-04
**Success Criteria** (what must be TRUE):

  1. One repeatable local check runs all five gates and reports a per-gate verdict; each gate has been observed failing when deliberately broken; and its verdict on `origin/main` agrees gate by gate with CI's for the gates CI runs
  2. Every row in `docs/spqr-properties.md` carries a `Source:` field, and the provenance gate resolves every citation — a row whose cited file, line range or spec section does not exist fails the gate
  3. `docs/proof-targets.md` records, for every catalog row, **one line per open obligation** (a partially proved row contributes its open half, its proved half recorded as out of the goal — `PROJECT.md` C1, ruled 2026-09-15) with that obligation's band, its C1/C2/C3 verdict and reason, its source citation and its support-lemma dependencies, and it names the resolved `origin/main` SHA its C1 column was classified against; the 22 proof targets — **work units, not rows** — and the demoted support lemmas are both derivable from it (CAT-03)
  4. The statement review is executable and binding: a documented cross-engine read-only review takes a **complete proposed Lean declaration** from its statement record plus only its cited source and a dated C1 evidence extract, and returns ACCEPT / REVISE / REJECT with a per-obligation record in a tracked log keyed on the statement's hash, and it has been run end to end on the two new canonicity statements (STRUCT-02a and STRUCT-02b). A support obligation can be reviewed under the reduced rubric without becoming a target
  5. `docs/spqr-properties.md` §11 carries a recorded decision for each of D1–D5, PROP-42's §5 statement matches the D1 decision, and PROP-30, PROP-47, PROP-50 and PROP-43 state the decided behaviour so Phases 4–5 can quote them verbatim
  6. No operative document cites a gate that does not exist in this repository, and `docs/ISSUE_TEMPLATE.md` is a per-property **PR** checklist naming the five real gates plus the catalog-and-index line

**Plans**: 9 plans in 2 PR boundaries (PR A: gates and provenance; PR B: target list, canonicity statements, D1–D5)

### Phase 2: Merge and Axiom Removal

**Goal**: The theorems that exist only on `la/lean-v1-protocol-proofs` are on `main`, axiom-free and deduplicated, so the refinement and trace work has a lemma base
**Depends on**: Phase 1 (gates; the D2 decision fixes the Greater-row statement of PROP-30)
**Requirements**: MERGE-01, MERGE-02, MERGE-03, MERGE-04, MERGE-05, MERGE-06, MERGE-07
**Success Criteria** (what must be TRUE):

  1. `Spqr/Specs/States/Send.lean` (one theorem per variant, PROP-21 send half), `States/Recv.lean` (Less and Greater rows including Ct2Sampled at `epoch + 1`) and the `send_key` epoch-decrease theorem (PROP-14) exist on `main`
  2. No axiom in `Spqr/Specs/` mentions `PolyEncoder.next_chunk`, `KeysUnsampled.send_hdr_chunk` or `HeaderReceived.send_ct1_chunk`; each has a theorem stating the conditions under which it succeeds — this removes three axioms from the trusted base and is the phase's main proof content
  3. No theorem name is defined twice across `Chain/AddEpoch.lean` vs `Chain/Chain/AddEpoch.lean` and `Chain/Key.lean` vs `Chain/ChainEpochDirection/Key.lean`, and `VecDeque.push_back_spec` is either imported from the Aeneas standard library or proved
  4. `#print axioms` on the merged `send`/`recv`/`send_key` theorems lists only builtin axioms and the documented stubs, and `sorry-manifest.txt` gains no line
  5. Catalog rows PROP-14, PROP-21 (send half) and PROP-30 (Less/Greater) read Proved rather than Proved (branch)

**Plans**: TBD

### Phase 3: Encoding Layer — Roundtrips and Canonicity

**Goal**: The wire format is proved to round-trip, the direction the catalog never stated is stated and settled, and the erasure-code axiom shrinks to `decoded_message` alone
**Depends on**: Phase 1 (gates, provenance, the reviewed canonicity statements). Independent of Phase 2 — these can run concurrently
**Requirements**: STRUCT-01, STRUCT-02a, STRUCT-02b, STRUCT-05
**Success Criteria** (what must be TRUE):

  1. `Message.deserialize (Message.serialize m i) = ok (m, i, _)` is a theorem (PROP-35) on the domain the code round-trips — `0 < m.epoch`, `Ct1Ack`'s Boolean is `true`, and the length bound `deserialize_spec` carries (`hlen`) instantiated at `serialize`'s output — resting on a new agreement lemma that the encoder model satisfies the decoder predicate (`varintBytes v` satisfies `varintBlockAt` at the offset it occupies, likewise `chunkBlockAt`), with the `at1` length accounting discharged. PROP-35's row already carries that domain: Phase 1 corrected it, because the unrestricted wording is false (`serialize` drops `Ct1Ack`'s Boolean; epoch 0 is rejected) and a false row is fixed in the PR that finds it. This phase proves the corrected statement rather than re-deriving its domain
  2. The canonicity work is **two** theorems, split on 2026-09-15 because the single "either/or" row tangled three different properties and mis-stated the equivalence relation:
     - **STRUCT-02a** exhibits the non-injectivity by witness: two distinct byte strings decoding to the same `(message, index)` (non-minimal LEB128, and the ten-byte block truncation `% 2^64` at `DecodeVarint.lean:44`), and two distinct messages with identical serialization (`Ct1Ack(false)`/`Ct1Ack(true)`, `serialize.rs:267`). A negative result discharges the row
     - **STRUCT-02b** proves `deserialize` injective on the canonical domain: minimal varints, no trailing bytes (`serialize.rs:274` accepts trailing data), in the image of `serialize`. It shares STRUCT-01's agreement lemma
     `Spqr/Specs/V1/Chunked/States/Serialize/DecodeVarint.lean:43` is cited as the source of the non-canonicity on both rows
  3. LEAN-ENC-2's axiom mentions only `PolyDecoder.decoded_message`; the surrounding encoder and decoder functions are theorems, and the "any `N` distinct codewords" statement is discharged down to that one axiom (§3.6)
  4. The catalog gains the STRUCT-02a and STRUCT-02b rows, each with its `Source:`, its ACCEPT review reference and its status; PROP-35's row carries its corrected domain; and LEAN-ENC-2's row records the narrowed axiom
  5. If STRUCT-02a's non-injectivity is reachable from a MAC'd byte string, that is reported as a finding and recorded as v2 SEC-01 — it is not silently proved around

**Plans**: TBD

### Phase 4: Transition Refinement

**Goal**: Every spec transition, dispatch row and integrity check of §2.5 is a theorem about the code path the catalog names
**Depends on**: Phase 2 (`Send.lean`/`Recv.lean` as lemma base), Phase 1 (D3/D4/D5 decisions, gates)
**Requirements**: REFINE-01, REFINE-02, REFINE-03, REFINE-04, REFINE-05, SITE-02, AXIOM-02
**Success Criteria** (what must be TRUE):

  1. PROP-47 transitions 1–5 and 6–13 each have a named theorem giving the spec's effect on epoch, authenticator and payload, and the statements match the D3 (`Ct1Ack(true)` emission and acceptance) and D4 (extra `Ek` acceptance) decisions from Phase 1
  2. PROP-30's Equal rows are theorems per variant: an unexpected payload type leaves the state unchanged with `key = None`, the expected type takes the transition
  3. PROP-49 is a theorem: the emitted `EpochSecret.epoch` is `state.epoch` in transition 7 and the pre-increment epoch in transition 5, while the new state carries `epoch + 1`
  4. PROP-25 is a theorem over all four state/chunk combinations reaching `Ct1Sent::recv_ek` — `ek_matches_header` is checked before `ek` is used and failure returns `ErroneousDataReceived` — resting on the PROP-3b axiom stated per AXIOM-02 from libcrux's FIPS 203 encoding rather than spec prose
  5. PROP-43 is a theorem against the D5 caller contract: failed `verify_hdr` in transition 6 and failed `verify_ct` in transition 5 make `States::recv` return `Err`, and `lib.rs` `recv` stores no new state on `Err`
  6. Support lemmas proved on the way (PROP-45 constants, PROP-48 decoder sizes) are recorded as support in `docs/proof-targets.md`, not promoted to phase goals

**Plans**: TBD

### Phase 5: Trace Properties

**Goal**: The per-transition results compose into statements about runs — epoch agreement, one key per epoch, epoch knowledge, and structural liveness
**Depends on**: Phase 4 (per-transition results), Phase 1 (D2 decision)
**Requirements**: TRACE-01, TRACE-02, TRACE-03, TRACE-04
**Success Criteria** (what must be TRUE):

  1. PROP-22 is a theorem for every `States` variant: `send` puts `state.epoch()` in `msg.epoch` and no `send` arm changes the epoch, so `t_snd = t_rcv = msg.epoch - 1`
  2. PROP-21's trace part is a theorem: a party never re-enters `HeaderReceived` or `EkSentCt1Received` at the same epoch, hence at most one key per epoch; and its recv half is a theorem: every `recv` arm other than `EkSentCt1Received` on a completing `Ct2` returns `key = None`
  3. PROP-23 is a theorem: a party at state epoch `e` has emitted keys for epochs `1..e-1` and `chain.add_epoch` was called with each, composed with the proved `add_epoch_spec` (PROP-9)
  4. PROP-50 is a theorem for the D2-decided behaviour: from `(KeysUnsampled_A(e), NoHeaderReceived_B(e))`, in-order delivery of every message reaches `(NoHeaderReceived_A(e+1), KeysUnsampled_B(e+1))`, and every reachable pair has a next step
  5. Each of the four carries an induction or reachability argument stated explicitly in the catalog text, so a reader can see what is quantified over runs rather than over a single call

**Plans**: TBD

### Phase 6: Session Key Consistency

**Goal**: Both parties are proved to derive the same epoch key, with the hand-written trusted base for it reduced to a single minimal axiom
**Depends on**: Phase 5 (PROP-23 epoch knowledge), Phase 4 (transitions 5 and 7), Phase 1 (gates)
**Requirements**: SITE-01, AXIOM-01, TRACE-05
**Success Criteria** (what must be TRUE):

  1. PROP-24 is a theorem at both KDF_OK sites (`HeaderReceived::send_ct1`, `EkSentCt1Received::recv_ct2`) fixing salt `0^32`, IKM `ss`, info `"Signal_PQCKA_V1_MLKEM768:SCKA Key" ‖ epoch_be` and length 32, plus a theorem that the two derivations are equal for equal `ss` and epoch
  2. PROP-3 is a single axiom binding `hdr`, `ek`, `dk` to one `generate` call, quantified only over the libcrux stubs, with component sizes derived from `generate_spec` rather than assumed
  3. PROP-1 is a theorem: both parties' `EpochSecret.secret` for epoch `t` equal `KDF_OK(ss, t)` for the same `ss`; `#print axioms` shows the PROP-3 axiom, `hkdf_to_slice_spec`, the libcrux stubs and no other hand-written axiom
  4. The catalog states PROP-1's hypotheses explicitly — it is a conditional theorem and must read as one
  5. The PROP-41 KDF_OK literal support lemma closes the label-prefix row as a by-product, recorded as support

**Plans**: TBD

### Phase 7: Chain Layer and Serialization

**Goal**: The `chain.rs` structural properties are proved, and the protobuf roundtrips are either proved or made honestly conditional on a classified trusted base
**Depends on**: Phase 1 (gates, provenance), Phase 2 (merged chain theorems)
**Requirements**: STRUCT-03, STRUCT-06, STRUCT-07, AXIOM-04, AXIOM-05, AXIOM-06
**Success Criteria** (what must be TRUE):

  1. PROP-10 is a theorem: advancing `send_epoch` pops links older than one epoch before `send_epoch`, clears the send seed of every earlier link, leaves receive seeds untouched, and `KeyHistory` entries are removed on `get` or trimmed by `gc`
  2. The prost classification (AXIOM-05) records, for each catalog property depending on the prost `Message` `sorry`s, the transitive path from `sorry-manifest.txt` and what a replacement model would have to provide — before PROP-37/38 are attempted, so their conditionality is known rather than discovered
  3. The **state-validity invariant PROP-37 needs is designed and written down here**, then PROP-37 is a theorem against it for all eleven `States` variants, including the chunked states whose per-state `into_pb`/`from_pb` specs do not yet exist, and the proof excludes cross-variant confusion rather than assuming it away. The unrestricted row is false for two independent reasons, both recorded by Phase 1 and neither sufficient alone: `pts_needed` is narrowed by `as u32` (`polynomial.rs:795`, `IntoPb.lean:289`), **and** the unchunked deserializers gate on stored byte-vector lengths (`src/v1/unchunked/send_ct/serialize.rs:84` requires 2080/960/1152 while `into_pb` copies verbatim), so a state with empty vectors serializes and then fails to deserialize. Phase 1 deliberately did **not** state the domain — representability alone was proposed and shown insufficient in plan review — so the invariant is this phase's design work: field lengths per deserializer, the variant-specific decoder-size checks (`src/v1/chunked/send_ct/serialize.rs:18`), and representability. PROP-37's catalog row is restated against it in the same PR as the theorem
  3a. Whether that invariant coincides with the reachable-state invariant of Phases 4–5 is answered explicitly rather than assumed: if it is strictly weaker, say so; if reachability is needed, cite the Phase 4/5 theorem that supplies it
  4. `States` protobuf injectivity is settled as a **corollary of criterion 3**, not a separate target (STRUCT-04 retired 2026-09-15): on criterion 3's validity domain, equal *successful* encodings imply equal states, by monadic composition with `from_pb` (`States.into_pb` returns `Result V1State`, `SrcTranslated/Funs.lean:10723`). Off the domain the counterexample families are stated rather than proved around — two states whose `pts_needed` differ by `2 ^ 32`, and two states differing in a byte-vector length the deserializer rejects — neither of which needs a prost `sorry`
  5. PROP-38 is either a theorem or an explicitly conditional statement whose hypotheses are the prost `sorry`s named in the AXIOM-05 classification, with the catalog row recording which of the two it is
  6. `MapCollectBridge.lean:70` and `DecodeState.lean:54` are each discharged or listed in §1 as trusted with a reason and an upstream reference (aeneas#1043), every remaining `sorry` in `Spqr/Specs/` appears in that list, and `potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275` is extracted or its assumed behaviour documented

**Plans**: TBD

### Phase 8: Catalog Regeneration

**Goal**: The catalog is a faithful rendering of `main`, with no status value left that nothing uses and no unsourced or unreviewed row
**Depends on**: Phases 2–7
**Requirements**: CAT-02
**Success Criteria** (what must be TRUE):

  1. The §12 index is regenerated against `main`, and every row's status is supported by a theorem, an axiom entry or a documented trusted item in §1
  2. `Proved (branch)` appears nowhere in `docs/spqr-properties.md`, and the paragraph describing the branch liveness axioms is removed or rewritten as history
  3. A fresh run of the five-gate check over `main` reproduces every Proved status; `sorry-manifest.txt` contains only entries listed in §1; the provenance gate passes on every row; and every Proved row has an ACCEPT review on record
  4. `docs/proof-targets.md` is reconciled against the outcome: every target is marked proved, conditional or not reached, with a reason for anything not reached

**Plans**: TBD

## Progress

**Execution Order:**
Phases execute in numeric order, except Phase 3 which may run concurrently with Phase 2:
1 → (2 ∥ 3) → 4 → 5 → 6 → 7 → 8

| Phase | Plans Complete | Status | Completed |
|-------|----------------|--------|-----------|
| 1. Gates, Provenance and the Reviewed Target List | 0/9 | Not started | - |
| 2. Merge and Axiom Removal | 0/TBD | Not started | - |
| 3. Encoding Layer — Roundtrips and Canonicity | 0/TBD | Not started | - |
| 4. Transition Refinement | 0/TBD | Not started | - |
| 5. Trace Properties | 0/TBD | Not started | - |
| 6. Session Key Consistency | 0/TBD | Not started | - |
| 7. Chain Layer and Serialization | 0/TBD | Not started | - |
| 8. Catalog Regeneration | 0/TBD | Not started | - |

## Notes

- **The goal is the number of non-trivial specs proved, not the number of rows
  closed.** Support lemmas from the evaluation and single-path bands get proved
  whenever a target needs them, and are recorded as support in
  `docs/proof-targets.md`. Promoting one to a phase goal is a scope error.

- **CAT-01 applies to every PR in every phase**, not only to Phase 1 where the
  checklist is written: the property's status, its section text and the §12 index
  change in the same PR as the theorem.

- **REV-01 is a precondition, not a review step.** Each phase's plan set must show,
  for every property it proves, that an ACCEPT statement review predates the proof
  work. A property proved without one is a process failure even if the theorem is
  correct.

- **Phase 1's DEV decisions are provisional**, recorded as "code as implemented is
  authoritative". If Signal later rules differently, re-stating the affected
  property is a new phase insertion, not a silent edit. The outward-facing note to
  Signal is deferred to v2 (DEV-05).

- **Two rows may legitimately end as conditional theorems**: STRUCT-07 (PROP-38,
  prost `sorry`s) and TRACE-05 (PROP-1, the PROP-3 axiom). Both must name their
  hypotheses in the catalog text, not only in a proof comment.

- **Phase 3 carries a known unknown.** The catalog states no roundtrip in the
  canonicity direction, and `DecodeVarint.lean:43` indicates the wire format is not
  injective. Phase 3 may therefore produce a negative result. That is a valid
  outcome and must be stated as one; whether it is exploitable is v2 SEC-01.
