/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.KeyHistory.KEY_SIZE
/-! # Spec theorem for `spqr::chain::{spqr::chain::KeyHistory}::remove`

`KeyHistory::remove` deletes a 36-byte record at `my_array_index` from `self.data` using
swap-remove:

1. If not last record (`my_array_index + 36 < self.data.len()`), copy last 36 bytes to
   target position, then truncate to `new_end = self.data.len() - 36`.
2. If last record, truncate to `my_array_index`.

Both paths shrink vector by exactly 36 bytes.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std

namespace spqr.chain.KeyHistory

/-- **Spec theorem for `spqr.chain.KeyHistory.remove`**:

• Removes 36-byte record at `my_array_index` from `self.data` via swap-remove.
• Returns updated `KeyHistory` with `data` shrunk by exactly 36 bytes.

**Postconditions**:

1. `result.data.length = self.data.length - 36`

2. Prefix preserved: `∀ i < my_array_index.val → result.data.val[i] = self.data.val[i]`

3. If **not** last (`my_array_index.val + 36 < self.data.length`):
   - Last record overwrites target; middle bytes unchanged

4. If **is** last (`my_array_index.val + 36 = self.data.length`):
   - `result.data.val = self.data.val.take my_array_index.val` -/
@[step]
theorem remove_spec (self : KeyHistory)
    (my_array_index : Usize)
    (_params : proto.pq_ratchet.ChainParams)
    (h_aligned : my_array_index + 36 ≤ self.data.length) :
    remove self my_array_index _params ⦃ fun (result : KeyHistory) =>
      result.data.length = self.data.length - 36 ∧
      (∀ i, i < my_array_index.val → result.data.val[i]! = self.data[i]!) ∧
      (my_array_index + 36 < self.data.length →
        result.data = (self.data.val.setSlice! my_array_index
            (self.data.val.drop (self.data.length - 36))).take (self.data.length - 36)) ∧
      (my_array_index + 36 = self.data.length →
        result.data = self.data.val.take my_array_index) ⦄ := by
  unfold remove
  step*
  split
  · rename_i h_lt
    simp only [alloc.vec.Vec.len, UScalar.lt_equiv] at h_lt
    simp only [alloc.vec.Vec.len]
    step
    simp only [alloc.vec.Vec.deref_mut, lift,
               core.slice.Slice.copy_within,
               core.ops.range.RangeFrom.Insts.CoreOpsRangeRangeBounds.start_bound,
               core.ops.range.RangeFrom.Insts.CoreOpsRangeRangeBounds.end_bound]
    simp only [Slice.length]
    step*
    split
    · step*
      simp only [_root_.Slice.copyWithinStart, _root_.Slice.copyWithinEnd] at *
      simp only [alloc.vec.Vec.length] at *
      refine ⟨?_, ?_, ?_, ?_⟩
      · grind
      · grind [Slice.setSlice!_val]
      · intro h_swap
        rw [v1_post]
        simp only [Slice.setSlice!_val]
        have hv : v.val = self.data.val.length - 36 := by
          scalar_tac
        rw [hv]
        congr 2
        rw [List.take_of_length_le]
        simp [List.length_drop]
      · scalar_tac
    · exfalso
      rename_i h_neg
      simp only [_root_.Slice.copyWithinStart,
        _root_.Slice.copyWithinEnd, not_and_or, not_le] at h_neg
      grind
  · rename_i h_nlt
    simp only [alloc.vec.Vec.len, UScalar.lt_equiv, not_lt] at h_nlt
    step*
    grind

end spqr.chain.KeyHistory
