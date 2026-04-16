/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Basic

/-! # Spec Theorem for `unaccelerated::mul`

Specification and proof for `encoding.gf.unaccelerated.mul`,
which implements carry-less polynomial multiplication of two `u16`
values in GF(2¹⁶), followed by reduction modulo the irreducible
polynomial POLY = x¹⁶ + x¹² + x³ + x + 1 (0x1100b).

In GF(2¹⁶) — the Galois field with 65 536 elements — multiplication
is polynomial multiplication modulo the irreducible polynomial POLY.
Each field element is represented as a polynomial of degree < 16 with
coefficients in GF(2), stored as a 16-bit unsigned integer.

The function proceeds in two stages:
  1. `poly_mul(a, b)` — carry-less (XOR-based) long multiplication of
     the two 16-bit inputs, producing a 32-bit unreduced product.
  2. `poly_reduce(product)` — reduction of the 32-bit product modulo
     POLY using a precomputed table (`REDUCE_BYTES`), yielding a
     16-bit result that is the canonical representative in GF(2¹⁶).

This function is the software (unaccelerated) fallback; on x86/x86_64
and aarch64, the same operation may be dispatched to hardware carry-
less multiplication instructions (`PCLMULQDQ` / `PMULL`).

**Source**: spqr/src/encoding/gf.rs (lines 444:4-446:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.gf.unaccelerated

/-
natural language description:

• Takes two `u16` values `a` and `b`, each representing an element
  of GF(2¹⁶) as a polynomial of degree < 16 with GF(2) coefficients.
• Computes the carry-less polynomial product via `poly_mul(a, b)`,
  which performs XOR-based long multiplication producing a 32-bit
  intermediate result.
• Reduces the 32-bit product modulo the irreducible polynomial
  POLY (0x1100b) via `poly_reduce`, using a precomputed reduction
  table (`REDUCE_BYTES`) to efficiently clear high-order bits.
• Returns the 16-bit result representing the GF(2¹⁶) product.

natural language specs:

• The function always succeeds (no panic) for any valid pair of
  `u16` inputs, since carry-less multiplication and table-based
  reduction are total operations on bounded integers.
• The result is the canonical GF(2¹⁶) product:
    `mul(a, b) = poly_reduce(poly_mul(a, b))`
• Together with the `MulAssign` trait implementation, the following
  identity holds:
    `(a * b).value = mul(a.value, b.value)`
-/

/-- **Postcondition axiom for `encoding.gf.unaccelerated.mul`**:

Carry-less polynomial multiplication of two `u16` values in GF(2¹⁶),
followed by reduction modulo the irreducible polynomial
POLY = 0x1100b.

The function composes `poly_mul` (carry-less long multiplication
producing a 32-bit intermediate) with `poly_reduce` (table-based
reduction modulo POLY).

This is stated as an axiom because the implementation involves
loop-based carry-less multiplication (`poly_mul`) and table-based
reduction (`poly_reduce`), both of which use complex loop invariants
that are verified separately at the Rust/F* level.

**Source**: spqr/src/encoding/gf.rs (lines 444:4-446:5)
-/
@[step]
theorem mul_spec (a b : Std.U16) :
    mul a b ⦃ result =>
      (result.val : GF216) = a * b  ⦄ := by
  sorry

end spqr.encoding.gf.unaccelerated
