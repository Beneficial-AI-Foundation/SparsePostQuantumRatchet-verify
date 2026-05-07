/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf
import Spqr.Specs.Encoding.Gf.GF16.SubAssign
/-! # Spec Theorem for `spqr::encoding::gf::{impl ops::Sub for GF16}::sub`

Specification and proof for `spqr.encoding.gf.GF16.Insts.CoreOpsArithSubGF16GF16.sub`,
which implements `Sub<GF16> for GF16` by delegating to the by-reference
`SubAssign<&GF16> for GF16` (i.e.
`CoreOpsArithSubAssignShared0GF16.sub_assign`), which itself forwards
to the by-reference `AddAssign<&GF16> for GF16`.

In GF(2¹⁶) — the Galois field with 65 536 elements — subtraction is
simply bitwise XOR of the two 16-bit underlying values.  This follows
from the fact that GF(2¹⁶) has characteristic 2, so every element is
its own additive inverse (`a + a = 0`), meaning subtraction and
addition coincide:
  `a - b = a + b = a ⊕ b`

Concretely, `sub self other` calls
`CoreOpsArithSubAssignShared0GF16.sub_assign self other`, which
ultimately computes `self.value ^^^ other.value` (bitwise XOR) and
wraps the result back into a `GF16`.

The by-value `Sub` introduces no additional logic beyond the
delegation, so its postcondition is inherited from the corresponding
`SubAssign` specification: lifting the underlying `u16` of the result
into `GF216 = GaloisField 2 16` via `Nat.toGF216` yields the GF(2¹⁶)
difference of the lifts of `self.value` and `other.value`.

Note that in GF(2¹⁶), addition and subtraction coincide:
  `a + b = a - b = a ⊕ b`
since every element is its own additive inverse (`a + a = 0`).

**Source**: spqr/src/encoding/gf.rs (lines 104:4-108:5)
-/

open Aeneas Aeneas.Std Result
open spqr.encoding.gf.unaccelerated

namespace spqr.encoding.gf.GF16.Insts.CoreOpsArithSubGF16GF16

/-
natural language description:

• Takes two `GF16` field elements `self` and `other`, each wrapping
  a `u16` value representing an element of GF(2¹⁶).
• Delegates immediately to the by-reference `sub_assign`:
    `CoreOpsArithSubAssignShared0GF16.sub_assign self other`
  which in turn calls `add_assign` (since subtraction = addition in
  GF(2¹⁶)), computing `self.value ^^^ other.value` (bitwise XOR).
• Returns the resulting `GF16` whose `value` field is the GF(2¹⁶)
  difference of the two inputs.

natural language specs:

• The function always succeeds (no panic) for any pair of `GF16`
  inputs, since XOR is a total operation on bounded integers.
• Lifting `result.value.val` into `GF216` via the canonical map
  `Nat.toGF216 = φ ∘ natToGF2Poly` yields the GF(2¹⁶) difference of
  the similarly-lifted inputs:
    `(result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 - other.value.val.toGF216`
  where the `-` on the right-hand side is subtraction in
  `GF216 = GaloisField 2 16` (which, in characteristic 2, coincides
  with addition).
-/

/-- **Spec and proof concerning `spqr.encoding.gf.GF16.Insts.CoreOpsArithSubGF16GF16.sub`**:

The by-value `Sub<GF16> for GF16` computes GF(2¹⁶) subtraction by
delegating to the by-reference `SubAssign<&GF16> for GF16`, which
ultimately performs bitwise XOR of the two underlying `u16` values.

The result satisfies the GF(2¹⁶)-level postcondition:

  `(result.value.val.toGF216 : GF216) =
       self.value.val.toGF216 - other.value.val.toGF216`

where `Nat.toGF216 n = φ (natToGF2Poly n)` interprets a natural
number as an element of `GF216 = GaloisField 2 16` via the chosen
ring homomorphism `φ : GF2Poly →+* GF216` that vanishes on
`POLY_GF2`.

The proof unfolds `sub` to expose the underlying `sub_assign` call
and discharges the resulting goal with `step*`, which applies the
already-registered `sub_assign_spec`.

**Source**: spqr/src/encoding/gf.rs (lines 104:4-108:5)
-/
@[step]
theorem sub_spec (self other : spqr.encoding.gf.GF16) :
    sub self other ⦃ (result : spqr.encoding.gf.GF16) =>
      (result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 - other.value.val.toGF216 ⦄ := by
  unfold sub
  step*

end spqr.encoding.gf.GF16.Insts.CoreOpsArithSubGF16GF16

/-! ## By-reference `Sub<&GF16> for GF16`

The by-reference `Sub<&GF16, Output = GF16> for GF16` takes `other`
by reference in the original Rust source.  In the Aeneas extraction
the reference is erased, so the Lean signature is identical to the
by-value variant.  The implementation delegates directly to the
by-reference `SubAssign<&GF16> for GF16` (i.e.
`CoreOpsArithSubAssignShared0GF16.sub_assign`), which computes
`self.value ^^^ other.value` (bitwise XOR).

Since the by-reference `Sub` introduces no additional logic beyond
the delegation, its postcondition is inherited from the corresponding
`SubAssign` specification.

**Source**: spqr/src/encoding/gf.rs (lines 118:4-122:5)
-/

namespace spqr.encoding.gf.GF16.Insts.CoreOpsArithSubShared0GF16GF16

/-
natural language description:

• Takes two `GF16` field elements `self` and `other`, each wrapping
  a `u16` value representing an element of GF(2¹⁶).
  In the original Rust source `other` is passed by reference
  (`&GF16`); after Aeneas extraction the reference is erased and
  both arguments are plain `GF16` values.
• Delegates immediately to the by-reference `sub_assign`:
    `CoreOpsArithSubAssignShared0GF16.sub_assign self other`
  which in turn calls `add_assign` (since subtraction = addition in
  GF(2¹⁶)), computing `self.value ^^^ other.value` (bitwise XOR).
• Returns the resulting `GF16` whose `value` field is the GF(2¹⁶)
  difference of the two inputs.

natural language specs:

• The function always succeeds (no panic) for any pair of `GF16`
  inputs, since XOR is a total operation on bounded integers.
• Lifting `result.value.val` into `GF216` via the canonical map
  `Nat.toGF216 = φ ∘ natToGF2Poly` yields the GF(2¹⁶) difference of
  the similarly-lifted inputs:
    `(result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 - other.value.val.toGF216`
  where the `-` on the right-hand side is subtraction in
  `GF216 = GaloisField 2 16` (which, in characteristic 2, coincides
  with addition).
-/

/-- **Spec and proof concerning `spqr.encoding.gf.GF16.Insts.CoreOpsArithSubShared0GF16GF16.sub`**:

The by-reference `Sub<&GF16> for GF16` computes GF(2¹⁶) subtraction by
delegating to the by-reference `SubAssign<&GF16> for GF16`, which
ultimately performs bitwise XOR of the two underlying `u16` values.

The result satisfies the GF(2¹⁶)-level postcondition:

  `(result.value.val.toGF216 : GF216) =
       self.value.val.toGF216 - other.value.val.toGF216`

where `Nat.toGF216 n = φ (natToGF2Poly n)` interprets a natural
number as an element of `GF216 = GaloisField 2 16` via the chosen
ring homomorphism `φ : GF2Poly →+* GF216` that vanishes on
`POLY_GF2`.

The proof unfolds `sub` to expose the underlying `sub_assign` call
and discharges the resulting goal with `step*`, which applies the
already-registered `sub_assign_spec`.

**Source**: spqr/src/encoding/gf.rs (lines 118:4-122:5)
-/
@[step]
theorem sub_spec (self other : spqr.encoding.gf.GF16) :
    sub self other ⦃ (result : spqr.encoding.gf.GF16) =>
      (result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 - other.value.val.toGF216 ⦄ := by
  unfold sub
  step*

end spqr.encoding.gf.GF16.Insts.CoreOpsArithSubShared0GF16GF16
