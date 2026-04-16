/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-! # Spec Theorem for `GF16::mul_assign` (by-value)

Specification and proof for `encoding.gf.GF16.Insts.CoreOpsArithMulAssignGF16.mul_assign`,
which implements `MulAssign<GF16> for GF16` by delegating to the
by-reference variant `MulAssign<&GF16> for GF16`.

In GF(2¹⁶) — the Galois field with 65 536 elements — multiplication is
polynomial multiplication modulo the irreducible polynomial
  `POLY = x¹⁶ + x¹² + x³ + x + 1`  (0x1100b).
This follows from the representation of GF(2¹⁶) as GF(2)[x] / (POLY),
where each element is a polynomial of degree < 16 with coefficients in
GF(2), stored as a 16-bit integer.

This simply forwards to `MulAssign<&GF16>::mul_assign`, which in turn
computes the GF(2¹⁶) product via carry-less polynomial multiplication
(`unaccelerated.poly_mul`) followed by reduction modulo POLY
(`reduce.poly_reduce`).

The by-value wrapper introduces no additional logic — it is
observationally identical to the by-reference version:
  `mul_assign_val(a, b) = mul_assign_ref(a, b)`

**Source**: spqr/src/encoding/gf.rs (lines 142:4-144:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.gf.GF16.Insts.CoreOpsArithMulAssignShared0GF16

/-
natural language description:

• Takes two `GF16` field elements `self` and `other`, each wrapping
  a `u16` value representing an element of GF(2¹⁶).
• Computes the GF(2¹⁶) product via carry-less polynomial multiplication
  of the underlying `u16` values, followed by reduction modulo the
  irreducible polynomial POLY (0x1100b):
    `self.value = unaccelerated::mul(self.value, other.value)`
• Returns the updated `self` with `self.value` replaced by the
  GF(2¹⁶) product.

natural language specs:

• The function always succeeds (no panic) for any valid pair of
  GF16 inputs, since polynomial multiplication and reduction are
  total operations on bounded integers.
• The result satisfies:
    `result.value = unaccelerated.mul self.value other.value`
• Together with the `Mul` trait implementation, the following
  identity holds:
    `(a * b).value = mul_assign(a, b).value`
-/

/-- **Postcondition axiom for
`encoding.gf.GF16.Insts.CoreOpsArithMulAssignShared0GF16.mul_assign`**:

The by-reference `MulAssign<&GF16> for GF16` computes GF(2¹⁶)
multiplication: carry-less polynomial multiplication of the two
underlying `u16` values followed by reduction modulo the irreducible
polynomial POLY (0x1100b).

The result satisfies:
  `∃ v, encoding.gf.unaccelerated.mul self.value other.value = ok v ∧
        result.value = v`

This is stated as an axiom because the by-reference `mul_assign` is
an external function (it dispatches to hardware-accelerated code on
x86/aarch64 and falls back to `unaccelerated::mul` otherwise; the
extraction only sees the unaccelerated path).

**Source**: spqr/src/encoding/gf.rs (lines 127:4-137:5)
-/
@[step]
axiom mul_assign_spec (self other : spqr.encoding.gf.GF16) :
    mul_assign self other ⦃ result =>
      ∃ v, encoding.gf.unaccelerated.mul self.value other.value = ok v ∧
        result.value = v ⦄

end spqr.encoding.gf.GF16.Insts.CoreOpsArithMulAssignShared0GF16

namespace spqr.encoding.gf.GF16.Insts.CoreOpsArithMulAssignGF16

/-- **Spec and proof concerning
`encoding.gf.GF16.Insts.CoreOpsArithMulAssignGF16.mul_assign`**:

The by-value `MulAssign<GF16> for GF16` delegates to the by-reference
`MulAssign<&GF16> for GF16`, which computes GF(2¹⁶) multiplication:
carry-less polynomial multiplication of the two underlying `u16` values
followed by reduction modulo the irreducible polynomial POLY (0x1100b).

The result satisfies:
  `∃ v, encoding.gf.unaccelerated.mul self.value other.value = ok v ∧
        result.value = v`

**Source**: spqr/src/encoding/gf.rs (lines 142:4-144:5)
-/
@[step]
theorem mul_assign_spec (self other : spqr.encoding.gf.GF16) :
    mul_assign self other ⦃ result =>
      ∃ v, encoding.gf.unaccelerated.mul self.value other.value = ok v ∧
        result.value = v ⦄ := by
  sorry

end spqr.encoding.gf.GF16.Insts.CoreOpsArithMulAssignGF16
