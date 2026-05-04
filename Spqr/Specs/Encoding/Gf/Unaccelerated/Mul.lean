/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf
import Spqr.Specs.Encoding.Gf.Reduce.PolyReduce
import Spqr.Specs.Encoding.Gf.Unaccelerated.PolyMul

/-! # Spec theorem for `spqr::encoding::gf::unaccelerated::mul`

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

The shared polynomial-library facts (`natToGF2Poly`, `POLY_GF2`,
`POLY_GF2_monic`, etc.) are imported from `Spqr.Math.Gf`.

**Source**: spqr/src/encoding/gf.rs (lines 444:4-446:5)
-/

open Aeneas Aeneas.Std Result
open Polynomial spqr.encoding.gf.reduce

namespace spqr.encoding.gf.unaccelerated

/-- **Polynomial-level postcondition for `encoding.gf.unaccelerated.mul`**:

Carry-less polynomial multiplication of two `u16` values in GF(2¹⁶),
followed by reduction modulo the irreducible polynomial
POLY = 0x1100b.

The function composes `poly_mul` (carry-less long multiplication
producing a 32-bit intermediate) with `poly_reduce` (table-based
reduction modulo POLY).

The result satisfies the polynomial-level specification:
  `natToGF2Poly result.val =
     (natToGF2Poly a.val * natToGF2Poly b.val) %ₘ POLY_GF2`

This follows from composing:
  1. `poly_mul_spec`:    `natToGF2Poly (poly_mul a b).val = natToGF2Poly a.val * natToGF2Poly b.val`
  2. `poly_reduce_spec`: `natToGF2Poly (poly_reduce v).val = (natToGF2Poly v.val) %ₘ POLY_GF2`

This establishes that `mul` computes multiplication in the quotient ring
  GF(2¹⁶) ≅ GF(2)[X] / (POLY_GF2)
at the polynomial level.

**Source**: spqr/src/encoding/gf.rs (lines 444:4-446:5)
-/
theorem mul_spec' (a b : Std.U16) :
    mul a b ⦃ result =>
      natToGF2Poly result.val =
        (natToGF2Poly a.val * natToGF2Poly b.val) %ₘ POLY_GF2 ⦄ := by
  unfold mul
  step*

/-- **GF216-level postcondition (provable, parametric)**:

For any ring-homomorphism `φ : (ZMod 2)[X] →+* GF216` that vanishes
on `POLY_GF2`, the result of `mul a b` corresponds — via `φ ∘
natToGF2Poly` — to the product of `a` and `b` in `GF216`.

Specializing `φ` to the canonical isomorphism (whose construction
requires irreducibility of `POLY_GF2` over `ZMod 2`, i.e. a finite-
field development we omit here) recovers the GF(2¹⁶) interpretation
of the result. -/
@[step]
theorem mul_spec
    (a b : Std.U16) :
    mul a b ⦃ result =>
      result.val.toGF216 = a.val.toGF216 * b.val.toGF216 ⦄ := by
  have hMonic : POLY_GF2.Monic := POLY_GF2_monic
  have h := mul_spec' a b
  unfold mul
  step*
  simp only [Nat.toGF216]
  have key :
      φ (natToGF2Poly result.val) =
        φ ((natToGF2Poly a.val * natToGF2Poly b.val) %ₘ POLY_GF2) := by
    have hPoly :
        natToGF2Poly result.val =
          (natToGF2Poly a.val * natToGF2Poly b.val) %ₘ POLY_GF2 := by
      simp_all
    rw [hPoly]
  rw [key, ringHom_modByMonic φ POLY_GF2 hMonic hφ, map_mul]

end spqr.encoding.gf.unaccelerated
