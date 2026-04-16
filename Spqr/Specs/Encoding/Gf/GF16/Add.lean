/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Basic
import Spqr.Specs.Encoding.Gf.GF16.AddAssign

/-! # Spec Theorem for `GF16::add` (Add trait, by-value)

Specification and proof for `encoding.gf.GF16.Insts.CoreOpsArithAddGF16GF16.add`,
which implements `Add<GF16> for GF16` by delegating to the
by-reference variant `AddAssign<&GF16> for GF16`.

In GF(2¹⁶) — the Galois field with 65 536 elements — addition is
simply bitwise XOR of the two 16-bit underlying values.  This follows
from the fact that GF(2¹⁶) has characteristic 2, so addition of
polynomial coefficients is addition in GF(2), which is XOR.

This simply forwards to `AddAssign<&GF16>::add_assign`, which in turn
computes `self.value ^= other.value` (bitwise XOR).

The by-value `Add` introduces no additional logic — it is
observationally identical to the by-reference version:
  `Add<GF16>::add(a, b) = Add<&GF16>::add(a, b)`

Note that in GF(2¹⁶), addition and subtraction coincide:
  `a + b = a - b = a ⊕ b`
since every element is its own additive inverse (`a + a = 0`).

**Source**: spqr/src/encoding/gf.rs (lines 53:4-57:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.gf.GF16.Insts.CoreOpsArithAddGF16GF16

/-
natural language description:

• Takes two `GF16` field elements `self` and `other`, each wrapping
  a `u16` value representing an element of GF(2¹⁶).
• Delegates immediately to the by-reference `add_assign`:
    `self.add_assign(&other)`
  which computes `self.value ^= other.value` (bitwise XOR).
• Returns the result as a new `GF16` value with `value` replaced by
  the GF(2¹⁶) sum.

natural language specs:

• The function always succeeds (no panic) for any valid pair of
  GF16 inputs, since XOR is a total operation on bounded integers.
• The result is identical to calling the by-reference
  `AddAssign<&GF16>::add_assign`:
    `add(a, b) = add_assign(a, b)`
• Together with the `AddAssign` trait implementation, the following
  identity holds:
    `(a + b).value = add_assign(a, b).value`
-/

@[step]
theorem add_spec (self other : spqr.encoding.gf.GF16) :
    add self other ⦃ result =>
      (result.value : GF216)= self.value + other.value.val ⦄ := by
  unfold add
  step*

end spqr.encoding.gf.GF16.Insts.CoreOpsArithAddGF16GF16
