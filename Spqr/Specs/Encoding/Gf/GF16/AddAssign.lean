/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf
import Mathlib.Data.Nat.Bitwise

/-! # Spec Theorem for `GF16::add_assign` (by-value)

Specification and proof for `encoding.gf.GF16.Insts.CoreOpsArithAddAssignGF16.add_assign`,
which implements `AddAssign<GF16> for GF16` by delegating to the
by-reference variant `AddAssign<&GF16> for GF16`.

In GF(2¹⁶) — the Galois field with 65 536 elements — addition is
simply bitwise XOR of the two 16-bit underlying values.  This follows
from the fact that GF(2¹⁶) has characteristic 2, so addition of
polynomial coefficients is addition in GF(2), which is XOR.

This simply forwards to `AddAssign<&GF16>::add_assign`, which in turn
computes `self.value ^= other.value` (bitwise XOR).

The by-value wrapper introduces no additional logic — it is
observationally identical to the by-reference version:
  `add_assign_val(a, b) = add_assign_ref(a, b)`

Note that in GF(2¹⁶), addition and subtraction coincide:
  `a + b = a - b = a ⊕ b`
since every element is its own additive inverse (`a + a = 0`).

**Source**: spqr/src/encoding/gf.rs (lines 40:4-43:5)
-/

open Aeneas Aeneas.Std Result
open spqr.encoding.gf.unaccelerated

namespace spqr.encoding.gf.GF16.Insts.CoreOpsArithAddAssignShared0GF16

/-
natural language description:

• Takes two `GF16` field elements `self` and `other`, each wrapping
  a `u16` value representing an element of GF(2¹⁶).
• Delegates immediately to the by-reference `add_assign`:
    `self.add_assign(&other)`
  which computes `self.value ^= other.value` (bitwise XOR).
• Returns the updated `self` with `self.value` replaced by the
  GF(2¹⁶) sum.

natural language specs:

• The function always succeeds (no panic) for any valid pair of
  GF16 inputs, since XOR is a total operation on bounded integers.
• The result is identical to calling the by-reference
  `AddAssign<&GF16>::add_assign`:
    `add_assign_val(a, b) = add_assign_ref(a, b)`
• Together with the `Add` trait implementation, the following
  identity holds:
    `(a + b).value = add_assign(a, b).value`
-/

/-- **Spec and proof concerning
`encoding.gf.GF16.Insts.CoreOpsArithAddAssignShared0GF16.add_assign`**:

The by-reference `AddAssign<&GF16> for GF16` computes GF(2¹⁶)
addition: bitwise XOR of the two underlying `u16` values.

The result satisfies the GF(2¹⁶)-level postcondition:

  `result.value.val.toGF216 =
       self.value.val.toGF216 + other.value.val.toGF216`

where `Nat.toGF216 n = φ (natToGF2Poly n)` interprets a natural
number as an element of `GF216 = GaloisField 2 16` via the chosen
ring homomorphism `φ : (ZMod 2)[X] →+* GF216` that vanishes on
`POLY_GF2`.

The proof reduces `result.value` to `self.value ^^^ other.value`,
applies `UScalar.val_xor` to push `.val` through `^^^`, and then
uses `natToGF2Poly_xor` together with the additivity of the ring
homomorphism `φ` (`map_add`).

**Source**: spqr/src/encoding/gf.rs (lines 28:4-31:5)
-/
@[step]
theorem add_assign_spec (self other : spqr.encoding.gf.GF16) :
    add_assign self other ⦃ result =>
      result.value.val.toGF216 =
        self.value.val.toGF216 + other.value.val.toGF216 ⦄ := by
  unfold add_assign
  step*
  simp_all only [UScalar.val_xor, Nat.toGF216, natToGF2Poly_xor, map_add]

end spqr.encoding.gf.GF16.Insts.CoreOpsArithAddAssignShared0GF16
