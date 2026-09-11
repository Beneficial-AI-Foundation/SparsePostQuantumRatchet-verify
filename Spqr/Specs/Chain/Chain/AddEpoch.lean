/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.Chain.CedForDirection
import Spqr.Specs.Lib.Direction.Switch
import Spqr.Specs.Kdf.HkdfToSlice
import Spqr.Crypto.Hkdf
/-!
# Spec theorem for `spqr::chain::{spqr::chain::Chain}::add_epoch`

Advances the chain to the next epoch: derives 96 bytes via HKDF from `next_root`/`epoch_secret`,
splits into new root (`[0..32]`), send (`[32..64]`) and recv (`[64..96]`) keys,
pushes a new `ChainEpoch`, and updates `current_epoch`.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr.chain.Chain

/-- **Spec theorem for `spqr.chain.Chain.add_epoch`**:

Derives HKDF output `genr8r` from `next_root`/`epoch_secret`, then:
- Preserves `dir`, `send_epoch`, `params`; sets `current_epoch = epoch_secret.epoch`.
- Sets `next_root = genr8r[0..32]`; appends a new `ChainEpoch` to `links`.
- Send/recv directions use `genr8r[32..64]`/`genr8r[64..96]` (swapped for B2A),
  each with counter 0 and empty key history. -/
@[step]
theorem add_epoch_spec (self : chain.Chain) (epoch_secret : EpochSecret)
    (h_epoch : epoch_secret.epoch.val = self.current_epoch.val + 1)
    (h_inv : self.links.length.val ≤ self.links.buf.val.length)
    (h_buf : self.links.buf.val.length < Usize.max) :
    add_epoch self epoch_secret ⦃ (result : chain.Chain) =>
      let genr8r := addEpochHkdfOutput self.next_root.val epoch_secret.secret.val
      result.dir = self.dir ∧
      result.current_epoch = epoch_secret.epoch ∧
      result.send_epoch = self.send_epoch ∧
      result.params = self.params ∧
      result.next_root.val = genr8r.slice 0 32 ∧
      result.next_root.length = 32 ∧
      result.links.length.val = self.links.length.val + 1 ∧
      result.links.head = self.links.head ∧
      match self.dir with
      | .A2B =>
        ∃ newEpoch : chain.ChainEpoch,
          result.links.buf.val = self.links.buf.val ++ [newEpoch] ∧
          newEpoch.send.ctr = 0#u32 ∧
          newEpoch.send.prev.data.length = 0 ∧
          newEpoch.send.next.val = genr8r.slice 32 64 ∧
          newEpoch.send.next.length = 32 ∧
          newEpoch.recv.ctr = 0#u32 ∧
          newEpoch.recv.prev.data.length = 0 ∧
          newEpoch.recv.next.val = genr8r.slice 64 96 ∧
          newEpoch.recv.next.length = 32
      | .B2A =>
        ∃ newEpoch : chain.ChainEpoch,
          result.links.buf.val = self.links.buf.val ++ [newEpoch] ∧
          newEpoch.send.ctr = 0#u32 ∧
          newEpoch.send.prev.data.length = 0 ∧
          newEpoch.send.next.val = genr8r.slice 64 96 ∧
          newEpoch.send.next.length = 32 ∧
          newEpoch.recv.ctr = 0#u32 ∧
          newEpoch.recv.prev.data.length = 0 ∧
          newEpoch.recv.next.val = genr8r.slice 32 64 ∧
          newEpoch.recv.next.length = 32 ⦄ := by
  unfold add_epoch
  match self.dir with
  | .A2B =>
    step*
    · grind
    · simp_all only [Array.make, Array.repeat_val,
      UScalar.ofNatCore_val_eq, List.reduceReplicate, alloc.vec.Vec.deref, Subtype.coe_eta,
      Array.val_to_slice, Slice.length, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
      hkdf_length, Array.from_slice_val, List.slice_zero_j, List.length_take, Nat.reduceLeDiff,
      inf_of_le_left, tsub_zero, alloc.vec.Vec.length, List.length_eq_zero_iff, addEpochHkdfOutput,
      chainAddEpochLabel, List.append_cancel_left_eq, List.cons.injEq, and_true, exists_eq_left',
      true_and]
      simp [List.slice_length, crypto.hkdf_length]
  | .B2A =>
    step*
    · grind
    · simp_all only [Array.make, Array.repeat_val,
      UScalar.ofNatCore_val_eq, List.reduceReplicate, alloc.vec.Vec.deref, Subtype.coe_eta,
      Array.val_to_slice, Slice.length, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
      hkdf_length, Array.from_slice_val, List.slice_zero_j, List.length_take, Nat.reduceLeDiff,
      inf_of_le_left, tsub_zero, alloc.vec.Vec.length, List.length_eq_zero_iff, addEpochHkdfOutput,
      chainAddEpochLabel, List.append_cancel_left_eq, List.cons.injEq, and_true, exists_eq_left',
      true_and]
      simp [List.slice_length, crypto.hkdf_length]


end spqr.chain.Chain
