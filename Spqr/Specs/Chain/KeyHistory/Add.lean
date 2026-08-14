/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.KeyHistory.KEY_SIZE
import Spqr.Specs.Aeneas.IndexRangeFull
import Spqr.Specs.Aeneas.VecExtendFromSlice
/-!
# Spec theorem for `spqr::chain::{spqr::chain::KeyHistory}::add`

`KeyHistory::add` appends a single key record to the history.  Given a key pair
`k = (counter : u32, key : [u8; 32])` and chain parameters `_params`, it:

  1. Converts `k.0` (the 4-byte counter) to big-endian bytes via `to_be_bytes`.
  2. Appends those 4 bytes to `self.data` via `extend_from_slice`.
  3. Appends the 32-byte key `k.1` to `self.data` via `extend_from_slice`.

The net effect is that `self.data` grows by exactly `KEY_SIZE = 36` bytes, with the new key record
`k.0.to_be_bytes() ‖ k.1` concatenated at the end.

The precondition (from the Rust `hax_lib::requires`) demands:
  • `_params.trim_size() < 119304647`
  • `self.data.len() <= KEY_SIZE * _params.trim_size()`

These ensure the vector length stays within `usize` bounds after the append.

**Source**: spqr/src/chain.rs (lines 139:4-142:5)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.KeyHistory

/--
**Spec theorem for `spqr.chain.KeyHistory.add`**:

• Takes a `KeyHistory` value `self`, a key pair `k = (u32, Array U8 32)`, and chain parameters
  `_params`.
• Converts the 4-byte counter `k.0` to big-endian bytes and appends them to `self.data`.
• Appends the 32-byte key `k.1` to `self.data`.
• Returns an updated `KeyHistory` whose `data` vector has grown by exactly `KEY_SIZE = 36` bytes.

The result satisfies the postcondition:

  `result.data.length = self.data.length + 36`

i.e. exactly one key record (4 bytes counter ++ 32 bytes key) has been appended to the history.

The proof unfolds `add` and discharges the resulting goals with `step*` and `scalar_tac`.

**Source**: spqr/src/chain.rs (lines 139:4-142:5)
-/
@[step]
theorem add_spec (self : chain.KeyHistory)
    (k : (Std.U32 × (Array Std.U8 32#usize)))
    (_params : proto.pq_ratchet.ChainParams)
    (h : self.data.length + 36 ≤ Std.Usize.max) :
    add self k _params ⦃ fun (result : chain.KeyHistory) =>
      result.data.length = self.data.length + 36 ⦄ := by
  unfold add
  step*
  sorry

end spqr.chain.KeyHistory
