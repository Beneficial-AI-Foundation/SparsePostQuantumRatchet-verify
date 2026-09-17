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
`epoch_idx_spec`, `index_mut_spec`, and `key_spec`.

**Source**: spqr/src/chain.rs -/
@[step]
theorem recv_key_spec (self : chain.Chain) (epoch : U64) (index : U32)
    (h_diff_fits : epoch.val ≤ self.current_epoch.val →
      self.current_epoch.val - epoch.val ≤ Usize.max)
    (h_wf : self.links.head.val + self.links.length.val ≤ self.links.buf.val.length)
    (h_target : epoch.val ≤ self.current_epoch.val →
      self.current_epoch.val - epoch.val < self.links.length.val →
      match self.links.buf.val[self.links.head.val + recvKeyIdx self epoch]? with
      | none => True
      | some ce =>
          ce.recv.next.length = 32 ∧
          index.val ≤ U32.max - 390451572 ∧
          (chain.maxOoo self.params).val < 390451572 ∧
          ce.recv.ctr.val ≤ U32.max - 390451572 ∧
          ce.recv.prev.data.length + 36 * (index.val - ce.recv.ctr.val) ≤ Usize.max ∧
          ce.recv.ctr < U32.max ∧
          ce.recv.prev.data.length % 36 = 0 ∧
          ce.recv.prev.data.length ≤ 36 * ce.recv.ctr.val ∧
          index.val + (chain.maxOoo self.params).val ≤ U32.max ∧
          System.Platform.numBits = 64) :
    recv_key self epoch index ⦃ (result :
        (core.result.Result (alloc.vec.Vec U8) Error) × chain.Chain) =>
      (epoch.val > self.current_epoch.val ∨
       self.current_epoch.val - epoch.val ≥ self.links.length.val →
         result.1 = core.result.Result.Err (Error.EpochOutOfRange epoch) ∧
         result.2 = self) ∧
      (epoch.val ≤ self.current_epoch.val ∧
       self.current_epoch.val - epoch.val < self.links.length.val →
         result.2.dir = self.dir ∧
         result.2.current_epoch = self.current_epoch ∧
         result.2.send_epoch = self.send_epoch ∧
         result.2.next_root = self.next_root ∧
         result.2.params = self.params ∧
         let phys := self.links.head.val + recvKeyIdx self epoch
         match self.links.buf.val[phys]? with
         | none => False
         | some ce =>
           (index = ce.recv.ctr →
             result.1 = core.result.Result.Err (Error.KeyAlreadyRequested index)) ∧
           (index < ce.recv.ctr →
             match result.1 with
             | core.result.Result.Err e =>
                 (e = Error.KeyTrimmed index ∧
                   index + (chain.maxOoo self.params).val < ce.recv.ctr) ∨
                 (e = Error.KeyAlreadyRequested index ∧
                   ce.recv.ctr ≤ index + (chain.maxOoo self.params).val ∧
                   (∀ k, k + 36 ≤ ce.recv.prev.data.length → k % 36 = 0 →
                     ce.recv.prev.data.val.slice k (k + 4) ≠
                       core.num.U32.to_be_bytes index))
             | core.result.Result.Ok out =>
                 ce.recv.ctr ≤ index + (chain.maxOoo self.params).val ∧
                 out.length = 32 ∧
                 (∃ off, off % 36 = 0 ∧
                   off + 36 ≤ ce.recv.prev.data.length ∧
                   ce.recv.prev.data.val.slice off (off + 4) =
                     (core.num.U32.to_be_bytes index).val ∧
                   (∀ k, k < off → k % 36 = 0 →
                     ce.recv.prev.data.val.slice k (k + 4) ≠
                       (core.num.U32.to_be_bytes index).val) ∧
                   out = ce.recv.prev.data.val.slice (off + 4) (off + 36))) ∧
           (index > ce.recv.ctr →
             index.val - ce.recv.ctr.val > (chain.maxJump self.params).val →
             result.1 = core.result.Result.Err
               (Error.KeyJump ce.recv.ctr index)) ∧
           (index > ce.recv.ctr →
             index.val - ce.recv.ctr.val ≤ (chain.maxJump self.params).val →
             match result.1 with
             | core.result.Result.Ok key =>
                 key.length = 32 ∧
                 key.val = (nextKeyHkdfOutput
                   (chain.ChainEpochDirection.iterChainSecret ce.recv.next.val ce.recv.ctr.val
                     (index.val - (ce.recv.ctr.val + 1)))
                   ⟨index.val, by scalar_tac⟩).drop 32
             | _ => False)) ⦄ := by
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
        self.links.head.val + (self.links.length.val - 1 - (self.current_epoch.val - epoch.val)) := by
      omega
    rw [List.getElem?_eq_getElem (by omega)] at h_tgt
    obtain ⟨ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10⟩ := h_tgt
    step*
    all_goals (
      have h_ge : self.links.buf.val[self.links.head.val + idx.val]? =
          some (self.links.buf.val[self.links.head.val + idx.val]'h_phys_lt) :=
        List.getElem?_eq_getElem h_phys_lt
      rw [h_ge] at ce_post
      have h_ce := ce_post.1; subst h_ce
      have : self.links.head.val + idx.val =
          self.links.head.val + (self.links.length.val - 1 - (self.current_epoch.val - epoch.val)) := by
        omega
      simp only [this] at *)
    all_goals first
    | assumption
    | (constructor
       · intro h_bad; exfalso; grind
       · intro _ _
         simp only [recvKeyIdx]
         rw [List.getElem?_eq_getElem (by omega)]
         refine ⟨fun h => (r1_post1 h).1, fun h => ?_, fun h1 h2 => (r1_post3 h1 h2).1,
                 fun h1 h2 => ?_⟩
         · obtain ⟨_, _, hm⟩ := r1_post2 h
           revert hm
           cases r1 with
           | Ok out =>
             intro ⟨h1, h2, _, _, off, h3, h4, h5, h6, h7, _, _, _⟩
             exact ⟨h1, h2, off, h3, h4, h5, h6, h7⟩
           | Err e =>
             intro h
             rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, _, h4⟩
             · exact Or.inl ⟨h1, h2⟩
             · exact Or.inr ⟨h1, h2, h4⟩
         · obtain ⟨key, h_ok, h_len, h_val⟩ := (r1_post4 h1 h2).1
           rw [h_ok]
           exact ⟨h_len, h_val⟩)

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
