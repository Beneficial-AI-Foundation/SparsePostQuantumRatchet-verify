/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf
/-! # Spec Theorem for `GF16::const_sub`

Specification and proof for `encoding.gf.GF16.const_sub`,
which implements GF(2¹⁶) subtraction on the `GF16` wrapper as
bitwise XOR of the two underlying `u16` values, re-wrapped into a
fresh `GF16`.

In GF(2¹⁶) — the Galois field with 65 536 elements — subtraction
coincides with addition: every element is its own additive inverse
(`a + a = 0`) since GF(2¹⁶) has characteristic 2.  Concretely, both
operations are bitwise XOR of the two 16-bit polynomial encodings:
  `a - b = a + b = a ⊕ b`

The function operates in a single stage:
  1. `self.value ^^^ other.value` — bitwise XOR of the two `u16`
     polynomial encodings, which corresponds to addition (=
     subtraction) of GF(2)-polynomial coefficients.

Unlike `unaccelerated::mul`, no reduction modulo the irreducible
polynomial POLY = x¹⁶ + x¹² + x³ + x + 1 is required: XOR of two
`u16` values is itself representable in 16 bits, so the resulting
GF(2) polynomial already has degree `< 16` and is the canonical
representative of its class in `(ZMod 2)[X] / (POLY_GF2)`.

The shared polynomial-library facts (`natToGF2Poly`, `POLY_GF2`,
`natToGF2Poly_xor`, `zmod2_poly_sub_eq_add`, `Nat.toGF216`, `φ`,
etc.) are imported from `Spqr.Math.Gf`.

**Source**: spqr/src/encoding/gf.rs (lines 566:4-570:5)
-/

open Aeneas Aeneas.Std Result
open Polynomial
open spqr.encoding.gf.unaccelerated

namespace spqr.encoding.gf.GF16

/-- **Polynomial-level postcondition for `encoding.gf.GF16.const_sub`**:

Bitwise XOR of two `u16` values in GF(2¹⁶), wrapped into a `GF16`.

At the GF(2)-polynomial level, XOR corresponds to polynomial
addition: each bit of the inputs is a coefficient in `ZMod 2`, and
XOR is exactly coefficient-wise addition modulo 2.  Since
`(ZMod 2)[X]` has characteristic 2, polynomial subtraction
coincides with polynomial addition, so XOR equally encodes
polynomial subtraction.

The result satisfies the polynomial-level specification:
  `natToGF2Poly result.value.val =
       natToGF2Poly self.value.val - natToGF2Poly other.value.val`

This follows from composing:
  1. `UScalar.val_xor`:        `(a ^^^ b).val = a.val ^^^ b.val`
  2. `natToGF2Poly_xor`:        XOR of naturals = addition of polys
  3. `zmod2_poly_sub_eq_add`:   in `(ZMod 2)[X]`, `a - b = a + b`

This establishes that `const_sub` computes subtraction in the
quotient ring
  GF(2¹⁶) ≅ GF(2)[X] / (POLY_GF2)
already at the polynomial level — no reduction modulo `POLY_GF2`
is necessary, since XOR of two `u16` values stays within 16 bits
and therefore corresponds to a polynomial of degree `< 16`.

**Source**: spqr/src/encoding/gf.rs (lines 566:4-570:5)
-/
theorem const_sub_spec' (self other : spqr.encoding.gf.GF16) :
    const_sub self other ⦃ result =>
      natToGF2Poly result.value.val =
        natToGF2Poly self.value.val - natToGF2Poly other.value.val ⦄ := by
  unfold const_sub
  step*
  simp_all only [UScalar.val_xor, natToGF2Poly_xor, zmod2_poly_sub_eq_add]

/-- **GF216-level postcondition (provable, parametric)**:

For the chosen ring-homomorphism `φ : (ZMod 2)[X] →+* GF216` (which
vanishes on `POLY_GF2`), the result of `const_sub self other`
corresponds — via `φ ∘ natToGF2Poly = Nat.toGF216` — to the
difference of `self.value.val` and `other.value.val` in `GF216`.

Specializing `φ` to the canonical isomorphism (whose construction
requires irreducibility of `POLY_GF2` over `ZMod 2`, i.e. the
finite-field development we omit here) recovers the GF(2¹⁶)
interpretation of the result.

Note that in GF(2¹⁶) addition and subtraction coincide, so this is
equivalently
  `result.value.val.toGF216 =
       self.value.val.toGF216 + other.value.val.toGF216`. -/
@[step]
theorem const_sub_spec
    (self other : spqr.encoding.gf.GF16) :
    const_sub self other ⦃ (result : spqr.encoding.gf.GF16) =>
      (result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 - other.value.val.toGF216 ⦄ := by
  unfold const_sub
  step*
  simp_all only [UScalar.val_xor, Nat.toGF216, natToGF2Poly_xor,
    ← zmod2_poly_sub_eq_add, map_sub]

end spqr.encoding.gf.GF16
