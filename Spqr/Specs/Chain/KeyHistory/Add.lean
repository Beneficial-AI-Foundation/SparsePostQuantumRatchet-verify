/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Aeneas.IndexRangeFull
import Spqr.Specs.Aeneas.VecExtendFromSlice
/-! # Spec theorem for `spqr::chain::{spqr::chain::KeyHistory}::add`

`KeyHistory::add` appends a single key record to the history.  Given a key pair
`k = (counter : u32, key : [u8; 32])` and chain parameters `_params`, it:

  1. Converts `k.0` (the 4-byte counter) to big-endian bytes via `to_be_bytes`.
  2. Appends those 4 bytes to `self.data` via `extend_from_slice`.
  3. Appends the 32-byte key `k.1` to `self.data` via `extend_from_slice`.

The net effect is that `self.data` grows by exactly `KEY_SIZE = 36` bytes, with the new key record
`k.0.to_be_bytes() ‖ k.1` concatenated at the end.

These ensure the vector length stays within `usize` bounds after the append.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std

namespace spqr.chain.KeyHistory

/-- **Spec theorem for `spqr.chain.KeyHistory.add`**:

The result satisfies the postconditions:

  1. `result.data.length = self.data.length + 36`
     — exactly one key record (4 bytes counter ++ 32 bytes key) has been appended.

  2. `result.data.val = self.data.val ++ (core.num.U32.to_be_bytes k.1).val ++ k.2.val`
     — the new data is the original data followed by the big-endian counter bytes and the key.

  3. `∀ i, i < self.data.length → result.data.val[i]! = self.data.val[i]!`
     — all pre-existing bytes are preserved (the append is non-destructive). -/
@[step]
theorem add_spec (self : chain.KeyHistory)
    (k : (U32 × (Array U8 32#usize)))
    (_params : proto.pq_ratchet.ChainParams)
    (h : self.data.length + 36 ≤ Usize.max) :
    add self k _params ⦃ fun (result : chain.KeyHistory) =>
      result.data.length = self.data.length + 36 ∧
      result.data = self.data ++ (core.num.U32.to_be_bytes k.1).val ++ k.2.val ∧
      (∀ i, i < self.data.length → result.data[i]! = self.data[i]!) ⦄ := by
  unfold add
  obtain ⟨i, a⟩ := k
  simp only
  step*
  all_goals grind [core.num.U32.to_be_bytes]

end spqr.chain.KeyHistory
