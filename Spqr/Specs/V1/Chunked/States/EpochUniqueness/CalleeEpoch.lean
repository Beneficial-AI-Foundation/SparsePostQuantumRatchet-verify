/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
import SrcTranslated.Funs
import SrcTranslated.FunsExternal
import Spqr.Auxiliary.Aeneas.Result
import Spqr.Auxiliary.Aeneas.Scalar
import Spqr.Specs.V1.Chunked.States.EpochUniqueness.UnchunkedEpoch

/-! # Epochs of the states returned by the chunked `send` / `recv` callees

Support lemmas for `Spqr.Specs.V1.Chunked.States.EpochUniqueness`, which proves that each party
outputs at most one key per epoch.

For each callee of an arm of `States::send` or `States::recv`, a lemma says that if the
function returns, the state it returns carries the epoch of its input. Two move to the next
epoch instead: `EkSentCt1Received::recv_ct2_chunk` on `Done`, and
`Ct2Sampled::recv_next_epoch`. Where the function also emits a key, the key carries the input
epoch. All are in the "if it returns `Ok`" form, so none needs a premise about the opaque KEM,
MAC, encoder or decoder stubs. The lemmas for the unchunked functions these callees reach are in
`Spqr.Specs.V1.Chunked.States.EpochUniqueness.UnchunkedEpoch`.

Transitions are numbered as in the state machine of [ML-KEM Braid] §2.5, drawn in its
Fig. 1 (p. 10) and marked `# Transition (n)` in the pseudocode of that section.

## References

* [ML-KEM Braid] R. Schmidt, *The ML-KEM Braid Protocol*, Rev. 1, last updated 2025-09-26.
  <https://signal.org/docs/specifications/mlkembraid/mlkembraid.pdf>

**Source**: spqr/src/v1/chunked/send_ek.rs, spqr/src/v1/chunked/send_ct.rs -/

open Aeneas Aeneas.Std Result
open core.result.Result.Insts.CoreOpsTry (branch_eq_continue)
open core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible (from_residual_ne_ok)

namespace spqr.v1.chunked.states.epoch_uniqueness

/-! ## `send` callees -/

theorem KeysUnsampled_send_hdr_chunk_epoch {R : Type} (i₁ : rand.rng.Rng R)
    (i₂ : rand_core.CryptoRng R) (self : v1.chunked.send_ek.KeysUnsampled) (rng : R)
    {r : (v1.chunked.send_ek.KeysSampled × encoding.Chunk) × R}
    (h : v1.chunked.send_ek.KeysUnsampled.send_hdr_chunk i₁ i₂ self rng = ok r) :
    r.1.1.uc.epoch = self.uc.epoch := by
  simp only [v1.chunked.send_ek.KeysUnsampled.send_hdr_chunk,
      v1.unchunked.send_ek.KeysUnsampled.send_header, bind_assoc, bind_eq_ok, Prod.exists,
      uncurry_apply_pair, ok.injEq, exists_and_right, Prod.mk.injEq, and_assoc, ↓existsAndEq,
      true_and, exists_and_left] at h
  obtain ⟨_, _, -, _, -, _, -, _, -, _, -, _, _, -, rfl⟩ := h
  rfl

theorem KeysSampled_send_hdr_chunk_epoch (self : v1.chunked.send_ek.KeysSampled)
    {r : v1.chunked.send_ek.KeysSampled × encoding.Chunk}
    (h : v1.chunked.send_ek.KeysSampled.send_hdr_chunk self = ok r) :
    r.1.uc.epoch = self.uc.epoch := by
  simp only [v1.chunked.send_ek.KeysSampled.send_hdr_chunk, bind_eq_ok, Prod.exists,
      uncurry_apply_pair, ok.injEq] at h
  obtain ⟨_, _, -, rfl⟩ := h
  rfl

theorem HeaderSent_send_ek_chunk_epoch (self : v1.chunked.send_ek.HeaderSent)
    {r : v1.chunked.send_ek.HeaderSent × encoding.Chunk}
    (h : v1.chunked.send_ek.HeaderSent.send_ek_chunk self = ok r) :
    r.1.uc.epoch = self.uc.epoch := by
  simp only [v1.chunked.send_ek.HeaderSent.send_ek_chunk, bind_eq_ok, Prod.exists,
      uncurry_apply_pair, ok.injEq] at h
  obtain ⟨_, _, -, rfl⟩ := h
  rfl

theorem Ct1Received_send_ek_chunk_epoch (self : v1.chunked.send_ek.Ct1Received)
    {r : v1.chunked.send_ek.Ct1Received × encoding.Chunk}
    (h : v1.chunked.send_ek.Ct1Received.send_ek_chunk self = ok r) :
    r.1.uc.epoch = self.uc.epoch := by
  simp only [v1.chunked.send_ek.Ct1Received.send_ek_chunk, bind_eq_ok, Prod.exists,
      uncurry_apply_pair, ok.injEq] at h
  obtain ⟨_, _, -, rfl⟩ := h
  rfl

/-- If `send_ct1_chunk` returns, the new state and the emitted key both carry the input
epoch. This is transition (7) of the ML-KEM Braid spec, §2.5, marked in
*HeaderReceived.Send* on p. 18. -/
theorem HeaderReceived_send_ct1_chunk_epoch {R : Type} (i₁ : rand.rng.Rng R)
    (i₂ : rand_core.CryptoRng R) (self : v1.chunked.send_ct.HeaderReceived) (rng : R)
    {r : (v1.chunked.send_ct.Ct1Sampled × encoding.Chunk × EpochSecret) × R}
    (h : v1.chunked.send_ct.HeaderReceived.send_ct1_chunk i₁ i₂ self rng = ok r) :
    r.1.1.uc.epoch = self.uc.epoch ∧ r.1.2.2.epoch = self.uc.epoch := by
  simp only [v1.chunked.send_ct.HeaderReceived.send_ct1_chunk, bind_eq_ok] at h
  obtain ⟨⟨⟨_, _, _⟩, _⟩, hs, h⟩ := h
  obtain ⟨h1, h2⟩ := HeaderReceived_send_ct1_epoch i₁ i₂ _ rng hs
  obtain ⟨_, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨_, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨⟨_, _⟩, -, h⟩ := bind_eq_ok.1 h
  cases h
  exact ⟨h1, h2⟩

theorem Ct1Sampled_send_ct1_chunk_epoch (self : v1.chunked.send_ct.Ct1Sampled)
    {r : v1.chunked.send_ct.Ct1Sampled × encoding.Chunk}
    (h : v1.chunked.send_ct.Ct1Sampled.send_ct1_chunk self = ok r) :
    r.1.uc.epoch = self.uc.epoch := by
  simp only [v1.chunked.send_ct.Ct1Sampled.send_ct1_chunk, bind_eq_ok, Prod.exists,
      uncurry_apply_pair, ok.injEq] at h
  obtain ⟨_, _, -, rfl⟩ := h
  rfl

theorem EkReceivedCt1Sampled_send_ct1_chunk_epoch
    (self : v1.chunked.send_ct.EkReceivedCt1Sampled)
    {r : v1.chunked.send_ct.EkReceivedCt1Sampled × encoding.Chunk}
    (h : v1.chunked.send_ct.EkReceivedCt1Sampled.send_ct1_chunk self = ok r) :
    r.1.uc.epoch = self.uc.epoch := by
  simp only [v1.chunked.send_ct.EkReceivedCt1Sampled.send_ct1_chunk, bind_eq_ok, Prod.exists,
      uncurry_apply_pair, ok.injEq] at h
  obtain ⟨_, _, -, rfl⟩ := h
  rfl

theorem Ct2Sampled_send_ct2_chunk_epoch (self : v1.chunked.send_ct.Ct2Sampled)
    {r : v1.chunked.send_ct.Ct2Sampled × encoding.Chunk}
    (h : v1.chunked.send_ct.Ct2Sampled.send_ct2_chunk self = ok r) :
    r.1.uc.epoch = self.uc.epoch := by
  simp only [v1.chunked.send_ct.Ct2Sampled.send_ct2_chunk, bind_eq_ok, Prod.exists,
      uncurry_apply_pair, ok.injEq] at h
  obtain ⟨_, _, -, rfl⟩ := h
  rfl

/-! ## `recv` callees -/

theorem KeysSampled_recv_ct1_chunk_epoch (self : v1.chunked.send_ek.KeysSampled)
    (epoch : Std.U64) (chunk : encoding.Chunk) {r : v1.chunked.send_ek.HeaderSent}
    (h : v1.chunked.send_ek.KeysSampled.recv_ct1_chunk self epoch chunk = ok r) :
    r.uc.epoch = self.uc.epoch := by
  simp only [v1.chunked.send_ek.KeysSampled.recv_ct1_chunk, v1.unchunked.send_ek.HeaderSent.send_ek,
      bind_tc_ok, uncurry_apply_pair, bind_eq_ok, ok.injEq, exists_and_right] at h
  obtain ⟨-, _, -, _, -, _, -, _, -, _, -, _, -, rfl⟩ := h
  rfl

theorem HeaderSent_recv_ct1_chunk_epoch (self : v1.chunked.send_ek.HeaderSent)
    (epoch : Std.U64) (chunk : encoding.Chunk) {r : v1.chunked.send_ek.HeaderSentRecvChunk}
    (h : v1.chunked.send_ek.HeaderSent.recv_ct1_chunk self epoch chunk = ok r) :
    match (generalizing := false) r with
    | .StillReceiving st => st.uc.epoch = self.uc.epoch
    | .Done st => st.uc.epoch = self.uc.epoch := by
  simp only [v1.chunked.send_ek.HeaderSent.recv_ct1_chunk, v1.unchunked.send_ek.EkSent.recv_ct1,
      bind_assoc, bind_tc_ok, bind_eq_ok, exists_and_right] at h
  obtain ⟨-, _, -, o, -, h⟩ := h
  cases o with
  | none =>
    simp only [ok.injEq] at h
    subst h
    rfl
  | some _ =>
    obtain ⟨_, -, h⟩ := bind_eq_ok.1 h
    simp only [ok.injEq] at h
    subst h
    rfl

theorem Ct1Received_recv_ct2_chunk_epoch (self : v1.chunked.send_ek.Ct1Received)
    (epoch : Std.U64) (chunk : encoding.Chunk) {r : v1.chunked.send_ek.EkSentCt1Received}
    (h : v1.chunked.send_ek.Ct1Received.recv_ct2_chunk self epoch chunk = ok r) :
    r.uc.epoch = self.uc.epoch := by
  simp only [v1.chunked.send_ek.Ct1Received.recv_ct2_chunk, bind_eq_ok, ok.injEq,
      exists_and_right] at h
  obtain ⟨-, _, -, _, -, _, -, -, _, -, _, -, _, -, _, -, rfl⟩ := h
  rfl

/-- If `recv_ct2_chunk` returns `Ok`, then on `StillReceiving` the state keeps the input
epoch, and on `Done` the key carries the input epoch and the new state the next one. The
`Done` case is transition (5) of the ML-KEM Braid spec, §2.5, marked in
*EkSentCt1Received.Receive* on p. 16. -/
theorem EkSentCt1Received_recv_ct2_chunk_epoch (self : v1.chunked.send_ek.EkSentCt1Received)
    (epoch : Std.U64) (chunk : encoding.Chunk)
    {r : v1.chunked.send_ek.EkSentCt1ReceivedRecvChunk}
    (h : v1.chunked.send_ek.EkSentCt1Received.recv_ct2_chunk self epoch chunk = ok (.Ok r)) :
    match (generalizing := false) r with
    | .StillReceiving st => st.uc.epoch = self.uc.epoch
    | .Done (st, k) => st.uc.epoch.val = self.uc.epoch.val + 1 ∧ k.epoch = self.uc.epoch := by
  simp only [v1.chunked.send_ek.EkSentCt1Received.recv_ct2_chunk, bind_eq_ok] at h
  obtain ⟨_, -, _, -, o, -, h⟩ := h
  cases o with
  | none =>
    simp only [ok.injEq, core.result.Result.Ok.injEq] at h
    subst h
    rfl
  | some ct2 =>
    simp only [bind_eq_ok, Prod.exists, uncurry_apply_pair] at h
    obtain ⟨_, -, mac, ct21, -, res, hres, cf, hcf, h⟩ := h
    cases cf with
    | Continue val =>
      obtain rfl := branch_eq_continue hcf
      obtain ⟨huc, hsec⟩ := EkSentCt1Received_recv_ct2_epoch _ _ _ hres
      obtain ⟨uc, sec⟩ := val
      simp only [uncurry_apply_pair, bind_eq_ok, ok.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨_, -, _, -, _, -, _, -, rfl⟩ := h
      exact ⟨huc, hsec⟩
    | Break res => exact (from_residual_ne_ok h).elim

theorem NoHeaderReceived_recv_hdr_chunk_epoch (self : v1.chunked.send_ct.NoHeaderReceived)
    (epoch : Std.U64) (chunk : encoding.Chunk)
    {r : v1.chunked.send_ct.NoHeaderReceivedRecvChunk}
    (h : v1.chunked.send_ct.NoHeaderReceived.recv_hdr_chunk self epoch chunk = ok (.Ok r)) :
    match (generalizing := false) r with
    | .StillReceiving st => st.uc.epoch = self.uc.epoch
    | .Done st => st.uc.epoch = self.uc.epoch := by
  simp only [v1.chunked.send_ct.NoHeaderReceived.recv_hdr_chunk, bind_eq_ok] at h
  obtain ⟨_, -, _, -, o, -, h⟩ := h
  cases o with
  | none =>
    simp only [ok.injEq, core.result.Result.Ok.injEq] at h
    subst h
    rfl
  | some hdr =>
    simp only [bind_eq_ok, Prod.exists, uncurry_apply_pair] at h
    obtain ⟨_, -, mac, hdr1, -, _, -, _, -, res, hres, cf, hcf, h⟩ := h
    cases cf with
    | Continue val =>
      obtain rfl := branch_eq_continue hcf
      have hval := NoHeaderReceived_recv_header_epoch _ _ _ _ hres
      simp only [bind_eq_ok] at h
      obtain ⟨_, -, h⟩ := h
      simp only [ok.injEq, core.result.Result.Ok.injEq] at h
      subst h
      exact hval
    | Break res => exact (from_residual_ne_ok h).elim

theorem Ct1Sampled_recv_ek_chunk_epoch (self : v1.chunked.send_ct.Ct1Sampled)
    (epoch : Std.U64) (chunk : encoding.Chunk) (ack : Bool)
    {r : v1.chunked.send_ct.Ct1SampledRecvChunk}
    (h : v1.chunked.send_ct.Ct1Sampled.recv_ek_chunk self epoch chunk ack = ok (.Ok r)) :
    match (generalizing := false) r with
    | .StillReceivingStillSending st => st.uc.epoch = self.uc.epoch
    | .StillReceiving st => st.uc.epoch = self.uc.epoch
    | .StillSending st => st.uc.epoch = self.uc.epoch
    | .Done st => st.uc.epoch = self.uc.epoch := by
  simp only [v1.chunked.send_ct.Ct1Sampled.recv_ek_chunk, bind_eq_ok] at h
  obtain ⟨_, -, o, -, h⟩ := h
  cases o with
  | none =>
    cases ack <;> simp only [Bool.false_eq_true, ↓reduceIte, ok.injEq,
      core.result.Result.Ok.injEq] at h <;> subst h <;> rfl
  | some ek =>
    simp only [bind_eq_ok] at h
    obtain ⟨res, hres, cf, hcf, h⟩ := h
    cases cf with
    | Continue val =>
      obtain rfl := branch_eq_continue hcf
      have hv := Ct1Sent_recv_ek_epoch _ _ _ hres
      cases ack
      · simp only [Bool.false_eq_true, ↓reduceIte, ok.injEq, core.result.Result.Ok.injEq] at h
        subst h
        exact hv
      · simp only [↓reduceIte, bind_eq_ok, Prod.exists, uncurry_apply_pair, ok.injEq,
          core.result.Result.Ok.injEq] at h
        obtain ⟨uc, _, _, hs, _, -, rfl⟩ := h
        exact (Ct1SentEkReceived_send_ct2_epoch _ hs).trans hv
    | Break _ => exact (from_residual_ne_ok h).elim

theorem EkReceivedCt1Sampled_recv_ct1_ack_epoch
    (self : v1.chunked.send_ct.EkReceivedCt1Sampled) (epoch : Std.U64)
    {r : v1.chunked.send_ct.Ct2Sampled}
    (h : v1.chunked.send_ct.EkReceivedCt1Sampled.recv_ct1_ack self epoch = ok r) :
    r.uc.epoch = self.uc.epoch := by
  simp only [v1.chunked.send_ct.EkReceivedCt1Sampled.recv_ct1_ack,
      v1.unchunked.send_ct.Ct1SentEkReceived.send_ct2, bind_assoc, bind_tc_ok, uncurry_apply_pair,
      bind_eq_ok, ok.injEq, exists_and_right] at h
  obtain ⟨-, _, -, _, -, _, -, _, -, rfl⟩ := h
  rfl

theorem Ct1Acknowledged_recv_ek_chunk_epoch (self : v1.chunked.send_ct.Ct1Acknowledged)
    (epoch : Std.U64) (chunk : encoding.Chunk)
    {r : v1.chunked.send_ct.Ct1AcknowledgedRecvChunk}
    (h : v1.chunked.send_ct.Ct1Acknowledged.recv_ek_chunk self epoch chunk = ok (.Ok r)) :
    match (generalizing := false) r with
    | .StillReceiving st => st.uc.epoch = self.uc.epoch
    | .Done st => st.uc.epoch = self.uc.epoch := by
  simp only [v1.chunked.send_ct.Ct1Acknowledged.recv_ek_chunk, bind_eq_ok] at h
  obtain ⟨_, -, o, -, h⟩ := h
  cases o with
  | none =>
    simp only [ok.injEq, core.result.Result.Ok.injEq] at h
    subst h
    rfl
  | some ek =>
    simp only [bind_eq_ok] at h
    obtain ⟨res, hres, cf, hcf, h⟩ := h
    cases cf with
    | Continue val =>
      obtain rfl := branch_eq_continue hcf
      have hv := Ct1Sent_recv_ek_epoch _ _ _ hres
      simp only [bind_eq_ok, Prod.exists, uncurry_apply_pair, ok.injEq,
        core.result.Result.Ok.injEq] at h
      obtain ⟨uc, _, _, hs, _, -, rfl⟩ := h
      exact (Ct1SentEkReceived_send_ct2_epoch _ hs).trans hv
    | Break _ => exact (from_residual_ne_ok h).elim

/-- If `recv_next_epoch` returns, the new `KeysUnsampled` state is one epoch later. This is
transition (13) of the ML-KEM Braid spec, §2.5, marked in *Ct2Sampled.Receive* on
p. 23. -/
theorem Ct2Sampled_recv_next_epoch_epoch (self : v1.chunked.send_ct.Ct2Sampled)
    (epoch : Std.U64) {r : v1.chunked.send_ek.KeysUnsampled}
    (h : v1.chunked.send_ct.Ct2Sampled.recv_next_epoch self epoch = ok r) :
    r.uc.epoch.val = self.uc.epoch.val + 1 := by
  simp only [v1.chunked.send_ct.Ct2Sampled.recv_next_epoch,
      v1.unchunked.send_ct.Ct2Sent.recv_next_epoch, bind_assoc, bind_tc_ok, bind_eq_ok, ok.injEq,
      exists_and_right] at h
  obtain ⟨_, ha, -, rfl⟩ := h
  exact UScalar.val_of_add_eq_ok ha

end spqr.v1.chunked.states.epoch_uniqueness
