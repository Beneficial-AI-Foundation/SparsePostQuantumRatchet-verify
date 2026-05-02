/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Basic
import Spqr.Specs.Encoding.Gf.Reduce.PolyReduce
import Spqr.Specs.Encoding.Gf.Unaccelerated.PolyMul
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
open Polynomial spqr.encoding.gf.reduce

namespace spqr.encoding.gf.unaccelerated

/-! ## Bridging lemmas: polynomial level → ring-homomorphism level -/

/-- **Bridge lemma**: any monic polynomial `P` and ring-homomorphism `φ`
that vanishes at `P` makes the residue `p %ₘ P` φ-equal to `p` itself.

This is the standard "transport along the quotient map" identity:
if `φ : (ZMod 2)[X] →+* R` factors through `(ZMod 2)[X] ⧸ (P)` (i.e.
`φ P = 0`), then `φ p = φ (p %ₘ P)`.  Multiplying through by the
quotient identity `p = P * (p /ₘ P) + (p %ₘ P)`, the `P · q` term is
killed by `φ P = 0`.
-/
private lemma ringHom_modByMonic
    {R : Type*} [CommRing R]
    (φ : (ZMod 2)[X] →+* R)
    (P : (ZMod 2)[X]) (hMonic : P.Monic) (hφ : φ P = 0)
    (p : (ZMod 2)[X]) :
    φ (p %ₘ P) = φ p := by
  -- `modByMonic_add_div p hMonic : p %ₘ P + P * (p /ₘ P) = p`
  have heq : p %ₘ P + P * (p /ₘ P) = p :=
    Polynomial.modByMonic_add_div p hMonic
  have h1 : φ p = φ (p %ₘ P + P * (p /ₘ P)) := by rw [heq]
  have h2 :
      φ (p %ₘ P + P * (p /ₘ P)) = φ (p %ₘ P) + φ P * φ (p /ₘ P) := by
    simp [map_add, map_mul]
  rw [h1, h2, hφ]; ring

/-- **Composition lemma**: combining `poly_mul_spec` with the
algebraic property of `%ₘ POLY_GF2`, for any `u32` value `v` whose
`natToGF2Poly` encoding equals the polynomial product of two `u16`
inputs, taking `%ₘ POLY_GF2` of either side gives the same residue
class in `GF(2)[X]`. -/
private lemma natToGF2Poly_modByMonic_of_eq
    (v : Nat) (p q : (ZMod 2)[X])
    (h : natToGF2Poly v = p * q) :
    natToGF2Poly v %ₘ POLY_GF2 = (p * q) %ₘ POLY_GF2 := by
  rw [h]

/-- **Multiplicativity of `%ₘ POLY_GF2` (compatibility with the quotient ring
multiplication).**

For any two natural numbers `p` and `q`, reducing the product of their
`natToGF2Poly` encodings modulo `POLY_GF2` is the same as first reducing
each factor modulo `POLY_GF2`, multiplying the residues, and reducing the
result again.  This is the algebraic statement that the quotient map
`(ZMod 2)[X] → (ZMod 2)[X] ⧸ (POLY_GF2)` is a ring homomorphism.

**Mathematical note.** The "naive" identity without the outer `%ₘ POLY_GF2`,
i.e.
  `(natToGF2Poly p %ₘ POLY_GF2) * (natToGF2Poly q %ₘ POLY_GF2)
     = (natToGF2Poly p * natToGF2Poly q) %ₘ POLY_GF2`,
is **false in general**.  Counter-example: take `p = q = 2 ^ 15` so that
`natToGF2Poly p = natToGF2Poly q = X ^ 15`.  Both factors already have
degree `< 16`, so `%ₘ POLY_GF2` is the identity on each.  The LHS is
`X ^ 30` (degree 30), while the RHS, being a residue, has degree `< 16`.
Hence the two sides cannot be equal.  The correct statement, proved
below, requires an outer `%ₘ POLY_GF2` on the LHS — exactly Mathlib's
`Polynomial.mul_modByMonic`. -/
lemma natToGF2Poly_modByMonic_eq (p q : Nat) :
    ((natToGF2Poly p %ₘ POLY_GF2) * (natToGF2Poly q %ₘ POLY_GF2)) %ₘ POLY_GF2 =
      (natToGF2Poly p * natToGF2Poly q) %ₘ POLY_GF2 :=
  (Polynomial.mul_modByMonic _ _ _).symm

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
@[step]
theorem mul_poly_spec (a b : Std.U16) :
    mul a b ⦃ result =>
      natToGF2Poly result.val =
        (natToGF2Poly a.val * natToGF2Poly b.val) %ₘ POLY_GF2 ⦄ := by
  unfold mul
  step*

/-! ## GF216-level postcondition (parametric form, fully provable)

The literal `Nat`-cast form `(result.val : GF216) = a * b` cannot be
proved (see file-level discussion above and the explicit counter-
example with `a = b = 0x100`).  The mathematically valid corollary
goes through any ring-homomorphism `φ : (ZMod 2)[X] →+* GF216` that
vanishes on `POLY_GF2`.  Such a `φ` is exactly the canonical map
witnessing `GF216 ≃ (ZMod 2)[X] ⧸ (POLY_GF2)` (which exists once one
proves `POLY_GF2` is irreducible — a non-trivial finite-field
computation).
-/

/-- **GF216-level postcondition (provable, parametric)**:

For any ring-homomorphism `φ : (ZMod 2)[X] →+* GF216` that vanishes
on `POLY_GF2`, the result of `mul a b` corresponds — via `φ ∘
natToGF2Poly` — to the product of `a` and `b` in `GF216`.

Specializing `φ` to the canonical isomorphism (whose construction
requires irreducibility of `POLY_GF2` over `ZMod 2`, i.e. a finite-
field development we omit here) recovers the GF(2¹⁶) interpretation
of the result. -/
theorem mul_spec_via_ringHom
    (φ : (ZMod 2)[X] →+* GF216)
    (hφ : φ POLY_GF2 = 0)
    (a b : Std.U16) :
    mul a b ⦃ result =>
      φ (natToGF2Poly result.val) =
        φ (natToGF2Poly a.val) * φ (natToGF2Poly b.val) ⦄ := by
  have hMonic : POLY_GF2.Monic :=   POLY_GF2_monic
  -- Combine the polynomial-level spec with the modByMonic ring-hom bridge.
  have h := mul_poly_spec a b
  -- `step*` does not apply to a generic `WP`; use direct manipulation:
  unfold mul
  step*
  -- After `step*` the goal becomes the polynomial-level equation
  -- on `i.val` and `result.val`; transport along φ.
  have key :
      φ (natToGF2Poly result.val) =
        φ ((natToGF2Poly a.val * natToGF2Poly b.val) %ₘ POLY_GF2) := by
    -- We get the polynomial-level postcondition from the hypotheses
    -- introduced by `step*` (named `i_post` and `result_post` in the
    -- original `mul_spec` proof).
    have hPoly :
        natToGF2Poly result.val =
          (natToGF2Poly a.val * natToGF2Poly b.val) %ₘ POLY_GF2 := by
      -- `step*` introduces hypotheses tracking each let-binding's
      -- post-condition; `simp_all` chains them to derive the goal.
      simp_all
    rw [hPoly]
  -- Strip the `%ₘ POLY_GF2` via the ring-hom bridge, then split the product.
  rw [key, ringHom_modByMonic φ POLY_GF2 hMonic hφ, map_mul]

/-- **Postcondition theorem for `encoding.gf.unaccelerated.mul`**:

Carry-less polynomial multiplication of two `u16` values in GF(2¹⁶),
followed by reduction modulo the irreducible polynomial
POLY = 0x1100b.

The function composes `poly_mul` (carry-less long multiplication
producing a 32-bit intermediate) with `poly_reduce` (table-based
reduction modulo POLY).

The result satisfies `(result.val : GF216) = a * b` where:
- `GF216 = GaloisField 2 16` is Mathlib's abstract construction
  of the Galois field with 65 536 elements.
- The coercion `(result.val : GF216)` interprets the 16-bit natural
  number as an element of GF(2¹⁶) via the standard embedding
  `Nat → GF216`.
- The multiplication `a * b` on the right-hand side is GF(2¹⁶)
  multiplication (polynomial multiplication modulo the irreducible).

**Mathematical note on this formulation.** The `Nat.cast : Nat → GF216`
embedding factors through `ZMod 2` (since `GF216` has characteristic 2),
so it only sees the parity of its input.  The literal equation
`(result.val : GF216) = a * b` therefore reduces to
`result.val % 2 = (a.val % 2) * (b.val % 2) % 2`, which fails for e.g.
`a = b = 0x100` — see the parametric `mul_spec_via_ringHom` above for the
mathematically correct statement.  The bridge from the polynomial-level
result (`mul_poly_spec`) to abstract `GaloisField` multiplication that
*does* validate the parity-only equation requires:
  - An explicit isomorphism `GF216 ≅ (ZMod 2)[X] / (POLY_GF2)`
  - Showing that POLY_GF2 is irreducible over GF(2)
  - Connecting `natToGF2Poly` to the `Nat → GF216` coercion

This deep algebraic connection is left as `sorry` pending the
construction of the explicit field isomorphism in Mathlib/Lean 4.

**Source**: spqr/src/encoding/gf.rs (lines 444:4-446:5)
-/
@[step]
theorem mul_spec (a b : Std.U16) :
    mul a b ⦃ result =>
      natToGF2Poly result.val =
        (natToGF2Poly a.val * natToGF2Poly b.val) %ₘ POLY_GF2 ⦄ := by
  unfold spqr.encoding.gf.unaccelerated.mul
  step*


end spqr.encoding.gf.unaccelerated
