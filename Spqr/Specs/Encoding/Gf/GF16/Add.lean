/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf
import Spqr.Specs.Encoding.Gf.GF16.AddAssign

/-! # Spec Theorem for `GF16::add` (Add trait, by-value)

Specification and proof for `encoding.gf.GF16.Insts.CoreOpsArithAddGF16GF16.add`,
which implements `Add<GF16> for GF16` by delegating to the by-value
`AddAssign<GF16> for GF16` (i.e.
`CoreOpsArithAddAssignShared0GF16.add_assign`), which itself forwards
to the by-reference `AddAssign<&GF16> for GF16`.

In GF(2¹⁶) — the Galois field with 65 536 elements — addition is
simply bitwise XOR of the two 16-bit underlying values.  This follows
from the fact that GF(2¹⁶) has characteristic 2, so addition of
polynomial coefficients is addition in GF(2), which is XOR.

Concretely, `add self other` calls
`CoreOpsArithAddAssignShared0GF16.add_assign self other`, which
ultimately computes `self.value ^^^ other.value` (bitwise XOR) and
wraps the result back into a `GF16`.

The by-value `Add` introduces no additional logic beyond the
delegation, so its postcondition is inherited from the corresponding
`AddAssign` specification: lifting the underlying `u16` of the result
into `GF216 = GaloisField 2 16` via `Nat.toGF216` yields the GF(2¹⁶)
sum of the lifts of `self.value` and `other.value`.

Note that in GF(2¹⁶), addition and subtraction coincide:
  `a + b = a - b = a ⊕ b`
since every element is its own additive inverse (`a + a = 0`).

**Source**: spqr/src/encoding/gf.rs (lines 53:4-57:5)
-/

open Aeneas Aeneas.Std Result
open spqr.encoding.gf.unaccelerated

namespace spqr.encoding.gf.GF16.Insts.CoreOpsArithAddGF16GF16

/-
natural language description:

• Takes two `GF16` field elements `self` and `other`, each wrapping
  a `u16` value representing an element of GF(2¹⁶).
• Delegates immediately to the by-value `add_assign`:
    `CoreOpsArithAddAssignShared0GF16.add_assign self other`
  which (via the by-reference variant) computes
  `self.value ^^^ other.value` (bitwise XOR).
• Returns the resulting `GF16` whose `value` field is the GF(2¹⁶)
  sum of the two inputs.

natural language specs:

• The function always succeeds (no panic) for any pair of `GF16`
  inputs, since XOR is a total operation on bounded integers.
• Lifting `result.value.val` into `GF216` via the canonical map
  `Nat.toGF216 = φ ∘ natToGF2Poly` yields the GF(2¹⁶) sum of the
  similarly-lifted inputs:
    `(result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 + other.value.val.toGF216`
  where the `+` on the right-hand side is addition in
  `GF216 = GaloisField 2 16`.
-/

/-- **Spec and proof concerning
`encoding.gf.GF16.Insts.CoreOpsArithAddGF16GF16.add`**:

The by-value `Add<GF16> for GF16` computes GF(2¹⁶) addition by
delegating to the by-value `AddAssign<GF16> for GF16`, which
ultimately performs bitwise XOR of the two underlying `u16` values.

The result satisfies the GF(2¹⁶)-level postcondition:

  `(result.value.val.toGF216 : GF216) =
       self.value.val.toGF216 + other.value.val.toGF216`

where `Nat.toGF216 n = φ (natToGF2Poly n)` interprets a natural
number as an element of `GF216 = GaloisField 2 16` via the chosen
ring homomorphism `φ : (ZMod 2)[X] →+* GF216` that vanishes on
`POLY_GF2`.

The proof unfolds `add` to expose the underlying `add_assign` call
and discharges the resulting goal with `step*`, which applies the
already-registered `add_assign_spec`.

**Source**: spqr/src/encoding/gf.rs (lines 53:4-57:5)
-/
@[step]
theorem add_spec (self other : spqr.encoding.gf.GF16) :
    add self other ⦃ result =>
      (result.value.val.toGF216 : GF216)= self.value.val.toGF216 + other.value.val.toGF216 ⦄ := by
  unfold add
  step*

end spqr.encoding.gf.GF16.Insts.CoreOpsArithAddGF16GF16
