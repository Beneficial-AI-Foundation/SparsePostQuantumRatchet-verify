/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.Chain.EpochIdx
import Spqr.Specs.Chain.ChainEpochDirection.Key
import Spqr.Specs.Aeneas.VecDerefMut
import Spqr.Specs.Chain.Chain.Defs
/-! # Spec theorem for `spqr::chain::{spqr::chain::Chain}::recv_key`

`Chain::recv_key` retrieves (or derives) the receiving key for a given `Epoch` and message
counter `index`.  Unlike `send_key`, it does **not** advance the send epoch, trim epochs, or
clear chain secrets — it simply locates the correct `ChainEpoch` entry in the `links` deque
and delegates to `ChainEpochDirection::key` on its `recv` direction.

  1. `epoch_idx` is called (via `?`).  If it fails — the epoch is in the future or has already
     been garbage-collected — `Err (EpochOutOfRange epoch)` is propagated and `self` is
     unchanged.
  2. Otherwise `epoch_idx` yields `idx = links.len() - 1 - (current_epoch - epoch)`.  The
     function mutably borrows `self.links[idx]`, calls `links[idx].recv.key(index, params)`,
     writes the updated `ChainEpochDirection` back, and returns the result.

The postcondition lifts the inner `ChainEpochDirection.key` result through the deque
indexing, stating that on success the `recv` field of the targeted `ChainEpoch` is updated
while everything else in the chain is preserved.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr.chain.Chain

/-- **Spec theorem for `spqr.chain.Chain.recv_key`**:

• Takes a `Chain` value `self`, an `Epoch` (= `U64`) value `epoch`, and a counter `index`
  (= `U32`).
• Calls `epoch_idx self epoch` to resolve the deque index.
  - On error (`EpochOutOfRange epoch`), the error is propagated and `self` is unchanged.
  - On success, `idx = self.links.length - 1 - (current_epoch - epoch)` is obtained.
• Mutably indexes into `self.links[idx]`, calls `ChainEpochDirection.key` on the `recv`
  direction with `(index, self.params)`, writes back the updated `ChainEpochDirection`,
  and returns the inner result.

The proof unfolds `recv_key`, then applies `step*` which chains the already-registered
`epoch_idx_spec`, `index_mut_spec`, and `key_spec`. -/
@[step]
theorem recv_key_spec (self : chain.Chain) (epoch : U64) (index : U32)
    (h_diff_fits : epoch.val ≤ self.current_epoch.val →
      self.current_epoch.val - epoch.val ≤ Usize.max)
    (h_wf : self.links.head.val + self.links.length.val ≤ self.links.buf.val.length)
    (h_target : epoch.val ≤ self.current_epoch.val →
      self.current_epoch.val - epoch.val < self.links.length.val →
      match self.links.buf.val[self.links.head.val + recvKeyIdx self epoch]? with
      | none => True
      | some ce => recvKeyPre self.params index ce) :
    recv_key self epoch index ⦃ (result :
        (core.result.Result (alloc.vec.Vec U8) Error) × chain.Chain) =>
      recvKeyPost self epoch index result.1 result.2 ⦄ := by
  unfold recvKeyPost chainFrame recvKeyEpochPost recvKeyAdvancePost
  simp only [recvKeyPre] at h_target
  unfold recv_key
  step
  simp only [r_post1]
  rcases r with idx | e
  · obtain ⟨h_le, h_back, h_idx⟩ := r_post2
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
    have h_phys_lt : self.links.head.val + idx.val < self.links.buf.val.length := by
      rw [h_idx]; omega
    have h_tgt := h_target h_le h_back
    simp only [recvKeyIdx] at h_tgt
    have h_idx_eq : self.links.head.val + idx.val =
        self.links.head.val +
        (self.links.length.val - 1 - (self.current_epoch.val - epoch.val)) := by
      omega
    rw [List.getElem?_eq_getElem (by omega)] at h_tgt
    obtain ⟨ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10⟩ := h_tgt
    step*
    all_goals (
      have h_ge : self.links.buf.val[self.links.head.val + idx.val]? =
          some (self.links.buf.val[self.links.head.val + idx.val]'h_phys_lt) :=
        List.getElem?_eq_getElem h_phys_lt
      rw [h_ge] at ce_post
      obtain ⟨h_ce, h_back_fn⟩ := ce_post
      subst h_ce
      have h_phys_rw : self.links.head.val + idx.val =
          self.links.head.val +
          (self.links.length.val - 1 - (self.current_epoch.val - epoch.val)) := by
        omega
      simp only [h_phys_rw] at *
      try (unfold cedKeyPost at r1_post
           obtain ⟨r1_post1, r1_post2, r1_post3, r1_post4⟩ := r1_post))
    all_goals first
    | assumption
    | (constructor
       · intro h_bad; exfalso; grind
       · intro h_le' h_lt'
         set ce := self.links.buf.val[self.links.head.val +
           (self.links.length.val - 1 - (self.current_epoch.val - epoch.val))]'(by omega)
         obtain ⟨h_buf_wb, h_hd_wb, h_ln_wb⟩ := h_back_fn { ce with recv := ced }
         simp only [recvKeyIdx]
         refine ⟨h_hd_wb, h_ln_wb, by rw [h_buf_wb, List.length_set],
                 by simp only [h_hd_wb, h_ln_wb, h_buf_wb, List.length_set]; exact h_wf,
                 fun j hj => by rw [h_buf_wb, List.getElem?_set_ne (by omega)], ?_⟩
         rw [List.getElem?_eq_getElem (by omega)]
         have h_ss : (self.links.buf.val.set
             (self.links.head.val +
               (self.links.length.val - 1 - (self.current_epoch.val - epoch.val)))
             { ce with recv := ced })[self.links.head.val +
               (self.links.length.val - 1 - (self.current_epoch.val - epoch.val))]? =
             some { ce with recv := ced } :=
           List.getElem?_set_self (by omega)
         rw [h_buf_wb, h_ss]
         refine ⟨rfl, fun h => ⟨(r1_post1 h).1, (r1_post1 h).2⟩, fun h => ?_,
                 fun h1 h2 => ⟨(r1_post3 h1 h2).1, (r1_post3 h1 h2).2⟩, fun h1 h2 => ?_⟩
         · exact r1_post2 h
         · obtain ⟨h_key, h_ctr, h_nlen, h_nval, h_palign, _, h_prevbd, h_clear,
                   h_usize, h_pregcbd, h_pgalign, h_kh0pg, h_gc⟩ := r1_post4 h1 h2
           exact ⟨h_key, h_ctr, h_nlen, h_nval, h_palign, h_prevbd, h_usize,
                  _, _, _, (⟨index.val - 1, by scalar_tac⟩ : U32), rfl, rfl, rfl,
                  h_pregcbd, h_pgalign, h_gc⟩)
  · obtain ⟨h_e, h_bad⟩ := r_post2
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    exact ⟨fun _ => ⟨congrArg _ h_e, trivial⟩,
           fun h12 h_lt => by
             exfalso
             rcases h_bad with h | h
             · exact Nat.not_le.mpr h h12
             · omega⟩

end spqr.chain.Chain
