/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Chain.Chain.RecvKey
import Spqr.Specs.Chain.ChainEpochDirection.Key32
import Spqr.Specs.Chain.Chain.Defs
/-! # 32-bit specialization of `recv_key_spec`

On 32-bit platforms the GC trim threshold `(maxOoo * 11/10 + 1) * 36` must fit
in `Usize.max = 2³² − 1`, which requires `maxOoo < 108458770` instead of the
64-bit bound `390451572`.

This file provides `recv_key_spec_32`, which uses the same postcondition
`recvKeyPost` as the 64-bit version but with the weaker precondition
`recvKeyPre32` (constant `108458770`, no platform hypothesis).

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr.chain.Chain

/-- **32-bit specialization of `recv_key_spec`**:

Same postcondition `recvKeyPost` as `recv_key_spec` but with the precondition
`recvKeyPre32` (constant `108458770`, no `System.Platform.numBits` hypothesis).

See `recv_key_spec` for full documentation of the postcondition.

**Source**: spqr/src/chain.rs -/
@[step]
theorem recv_key_spec_32 (self : chain.Chain) (epoch : U64) (index : U32)
    (h_diff_fits : epoch.val ≤ self.current_epoch.val →
      self.current_epoch.val - epoch.val ≤ Usize.max)
    (h_wf : self.links.head.val + self.links.length.val ≤ self.links.buf.val.length)
    (h_target : epoch.val ≤ self.current_epoch.val →
      self.current_epoch.val - epoch.val < self.links.length.val →
      match self.links.buf.val[self.links.head.val + recvKeyIdx self epoch]? with
      | none => True
      | some ce => recvKeyPre32 self.params index ce) :
    recv_key self epoch index ⦃ (result :
        (core.result.Result (alloc.vec.Vec U8) Error) × chain.Chain) =>
      recvKeyPost self epoch index result.1 result.2 ⦄ := by
  unfold recvKeyPost chainFrame recvKeyEpochPost
  simp only [recvKeyPre32] at h_target
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
    obtain ⟨ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9⟩ := h_tgt
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
      simp only [h_phys_rw] at *)
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
         exact ⟨rfl, r1_post⟩)
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
