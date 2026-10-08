/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
import SrcTranslated.Funs
import SrcTranslated.FunsExternal
import Spqr.Auxiliary.Aeneas.Result
import Spqr.Auxiliary.Aeneas.Scalar

/-! # Epochs of the states returned by the unchunked callees of the chunked states

Support lemmas for `Spqr.Specs.Braid.Scka.EpochUniqueness.CalleeEpoch`. The chunked
`send_ek` and `send_ct` states wrap an unchunked state `uc`, and their transitions call
`NoHeaderReceived::recv_header`, `EkSentCt1Received::recv_ct2`, `Ct1Sent::recv_ek`,
`Ct1SentEkReceived::send_ct2` and `HeaderReceived::send_ct1` of the unchunked layer. For each,
a lemma says that if the function returns, the state it returns carries the epoch of its
input, except `EkSentCt1Received::recv_ct2`, which moves to the next epoch. Where the function
also emits a key, the key carries the input epoch. All are in the "if it returns `Ok`" form.

**Source**: spqr/src/v1/unchunked/send_ek.rs, spqr/src/v1/unchunked/send_ct.rs -/

open Aeneas Aeneas.Std Result
open core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible (from_residual_ne_ok)

namespace spqr.v1.chunked.states.epoch_uniqueness

theorem NoHeaderReceived_recv_header_epoch (self : v1.unchunked.send_ct.NoHeaderReceived)
    (epoch : Std.U64) (hdr mac : alloc.vec.Vec Std.U8)
    {r : v1.unchunked.send_ct.HeaderReceived}
    (h : v1.unchunked.send_ct.NoHeaderReceived.recv_header self epoch hdr mac = ok (.Ok r)) :
    r.epoch = self.epoch := by
  simp only [v1.unchunked.send_ct.NoHeaderReceived.recv_header, bind_eq_ok] at h
  obtain ⟨_, -, res, -, cf, hcf, h⟩ := h
  cases cf with
  | Continue _ =>
    simp only [ok.injEq, core.result.Result.Ok.injEq] at h
    subst h
    rfl
  | Break _ => exact (from_residual_ne_ok h).elim

theorem EkSentCt1Received_recv_ct2_epoch (self : v1.unchunked.send_ek.EkSentCt1Received)
    (ct2 mac : alloc.vec.Vec Std.U8)
    {r : v1.unchunked.send_ct.NoHeaderReceived × EpochSecret}
    (h : v1.unchunked.send_ek.EkSentCt1Received.recv_ct2 self ct2 mac = ok (.Ok r)) :
    r.1.epoch.val = self.epoch.val + 1 ∧ r.2.epoch = self.epoch := by
  simp only [v1.unchunked.send_ek.EkSentCt1Received.recv_ct2, bind_eq_ok] at h
  obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, cf, -, h⟩ := h
  cases cf with
  | Continue _ =>
    simp only [bind_eq_ok] at h
    obtain ⟨i, hi, _, -, h⟩ := h
    simp only [ok.injEq, core.result.Result.Ok.injEq] at h
    subst h
    exact ⟨UScalar.val_of_add_eq_ok hi, rfl⟩
  | Break _ => exact (from_residual_ne_ok h).elim

theorem Ct1Sent_recv_ek_epoch (self : v1.unchunked.send_ct.Ct1Sent) (epoch : Std.U64)
    (ek : alloc.vec.Vec Std.U8) {r : v1.unchunked.send_ct.Ct1SentEkReceived}
    (h : v1.unchunked.send_ct.Ct1Sent.recv_ek self epoch ek = ok (.Ok r)) :
    r.epoch = self.epoch := by
  simp only [v1.unchunked.send_ct.Ct1Sent.recv_ek, bind_eq_ok] at h
  obtain ⟨_, -, b, -, h⟩ := h
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, ok.injEq,
    core.result.Result.Ok.injEq, reduceCtorEq] at h
  subst h
  rfl

theorem Ct1SentEkReceived_send_ct2_epoch (self : v1.unchunked.send_ct.Ct1SentEkReceived)
    {r : v1.unchunked.send_ct.Ct2Sent × alloc.vec.Vec Std.U8 × alloc.vec.Vec Std.U8}
    (h : v1.unchunked.send_ct.Ct1SentEkReceived.send_ct2 self = ok r) :
    r.1.epoch = self.epoch := by
  simp only [v1.unchunked.send_ct.Ct1SentEkReceived.send_ct2, bind_eq_ok, ok.injEq] at h
  obtain ⟨_, -, _, -, _, -, rfl⟩ := h
  rfl

/-- If `send_ct1` returns, the new state and the emitted key both carry the input epoch. -/
theorem HeaderReceived_send_ct1_epoch {R : Type} (i₁ : rand.rng.Rng R)
    (i₂ : rand_core.CryptoRng R) (self : v1.unchunked.send_ct.HeaderReceived) (rng : R)
    {r : (v1.unchunked.send_ct.Ct1Sent × alloc.vec.Vec Std.U8 × EpochSecret) × R}
    (h : v1.unchunked.send_ct.HeaderReceived.send_ct1 i₁ i₂ self rng = ok r) :
    r.1.1.epoch = self.epoch ∧ r.1.2.2.epoch = self.epoch := by
  simp only [v1.unchunked.send_ct.HeaderReceived.send_ct1, bind_eq_ok] at h
  obtain ⟨⟨⟨_, _, _⟩, _⟩, -, h⟩ := h
  iterate 9 obtain ⟨_, -, h⟩ := bind_eq_ok.1 h
  simp only [ok.injEq] at h
  subst h
  exact ⟨rfl, rfl⟩

end spqr.v1.chunked.states.epoch_uniqueness
