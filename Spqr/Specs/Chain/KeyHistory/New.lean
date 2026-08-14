/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.KeyHistory.KEY_SIZE
/-!
# Spec theorem for `spqr::chain::{spqr::chain::KeyHistory}::new`

`KeyHistory::new` constructs a fresh, empty `KeyHistory`.  The backing `Vec<u8>` is created with
`Vec::with_capacity(KEY_SIZE * 2)`, pre-allocating room for two key records (each 36 bytes) but
containing no data yet.

  • The returned `KeyHistory` has an empty `data` vector (`data.length = 0`).
  • No keys are stored, so the logical history model is empty.

The function is infallible for the extracted code: `KEY_SIZE` evaluates to `36`, and
`36 * 2 = 72` fits in `usize`, so the capacity computation cannot overflow.

**Source**: spqr/src/chain.rs (lines 132:4-136:5)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.KeyHistory

/--
**Spec theorem for `spqr.chain.KeyHistory.new`**:

• Allocates a new `KeyHistory` with an empty `data` vector.
• The backing vector is created via `Vec::with_capacity(KEY_SIZE * 2)` where `KEY_SIZE = 36`,
  giving an initial capacity of 72 bytes, but the vector length is 0.
• The function always succeeds (no overflow), since `36 * 2 = 72` is well within `usize` bounds.

The result satisfies the postcondition:

  `result.data.length = 0`

i.e. the `KeyHistory` is initially empty, containing no stored key records.

The proof unfolds `new`, applies the already-registered `KEY_SIZE_spec` via `step*`, and
discharges the remaining arithmetic with `scalar_tac`.

**Source**: spqr/src/chain.rs (lines 132:4-136:5)
-/
@[step]
theorem new_spec :
    new ⦃ fun (result : chain.KeyHistory) =>
      result.data.length = 0 ⦄ := by
  unfold new
  step*
  simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new, alloc.vec.Vec.length]

end spqr.chain.KeyHistory
