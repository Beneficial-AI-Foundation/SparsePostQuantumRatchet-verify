/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::empty_state`

`empty_state` constructs the canonical V0 (disabled) protocol state: an empty `Vec<u8>`.  When the
SPQR protocol version is `V0` (i.e., `Version::DISABLED`), the serialized state is simply an empty
byte vector — no protobuf encoding is needed, and no key material is generated.

This function is used by `initial_state` when `params.version = V0` and by `decode_state` as the
interpretation of an empty byte slice.

**Source**: spqr/src/lib.rs (lines 47:0-49:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.empty_state`**:

• Takes no arguments.
• Returns `ok (Vec.new U8)` — a freshly allocated empty vector.
• The function always succeeds (no panic, no allocation failure in the Aeneas model).

The result satisfies the emptiness postcondition:

  `result.val = []`

i.e., the returned vector contains no bytes, representing the V0 (disabled) protocol state. -/
@[step]
theorem empty_state_spec :
    empty_state ⦃ (result : alloc.vec.Vec U8) =>
      result.val = [] ⦄ := by
  unfold empty_state
  simp [alloc.vec.Vec.new]

end spqr
