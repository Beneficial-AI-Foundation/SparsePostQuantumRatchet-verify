/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf
import Spqr.Specs.Encoding.Gf.Unaccelerated.Mul

/-! # Spec Theorem for `unaccelerated::mul2`

Specification and proof for `encoding.gf.unaccelerated.mul2`,
which performs *two* GF(2¹⁶) multiplications sharing a common left
operand:

  `mul2(a, b1, b2) = (mul(a, b1), mul(a, b2))`

This is the software (unaccelerated) fallback for the "double-product"
primitive used by higher-level encoding routines; on x86/x86_64 and
aarch64 the same operation may be dispatched to a fused hardware
carry-less multiplication kernel.  The semantics are nevertheless
exactly that of running `unaccelerated.mul` twice with the same `a`,
once against each `bi`.

Each component of the result is therefore the canonical GF(2¹⁶)
representative of the polynomial product, obtained by composing
  1. `poly_mul`     — carry-less (XOR-based) long multiplication, then
  2. `poly_reduce`  — table-driven reduction modulo
                      POLY = x¹⁶ + x¹² + x³ + x + 1 (0x1100b).

The shared polynomial-library facts (`natToGF2Poly`, `POLY_GF2`,
`POLY_GF2_monic`, `ringHom_modByMonic`, etc.) are imported from
`Spqr.Math.Gf`; the per-factor postconditions (`mul_spec'`,
`mul_spec`) are imported from `Spqr.Specs.Encoding.Gf.Unaccelerated.Mul`.

**Source**: spqr/src/encoding/gf.rs (lines 436:4-438:5)
-/

open Aeneas Aeneas.Std Result
open Polynomial

namespace spqr.encoding.gf.unaccelerated

/-- **Polynomial-level postcondition for `encoding.gf.unaccelerated.mul2`**:

`mul2 a b1 b2` performs two independent GF(2¹⁶) multiplications that
share the left operand `a`.  Each component of the returned pair
satisfies the polynomial-level specification of `mul`:

  `natToGF2Poly result.1.val =
     (natToGF2Poly a.val * natToGF2Poly b1.val) %ₘ POLY_GF2`
  `natToGF2Poly result.2.val =
     (natToGF2Poly a.val * natToGF2Poly b2.val) %ₘ POLY_GF2`

This is an immediate consequence of `mul_spec'` applied componentwise
along the `do`-block in the extracted Lean source.

**Source**: spqr/src/encoding/gf.rs (lines 436:4-438:5)
-/
theorem mul2_spec' (a b1 b2 : Std.U16) :
    mul2 a b1 b2 ⦃ result =>
      natToGF2Poly result.1.val =
        (natToGF2Poly a.val * natToGF2Poly b1.val) %ₘ POLY_GF2 ∧
      natToGF2Poly result.2.val =
        (natToGF2Poly a.val * natToGF2Poly b2.val) %ₘ POLY_GF2 ⦄ := by
  unfold mul2
  have h1 := mul_spec' a b1
  have h2 := mul_spec' a b2
  step*

/-- **GF216-level postcondition (provable, parametric)**:

For any ring-homomorphism `φ : (ZMod 2)[X] →+* GF216` that vanishes
on `POLY_GF2`, both components of `mul2 a b1 b2` correspond — via
`φ ∘ natToGF2Poly` — to the products `a · b1` and `a · b2`
in `GF216`.

Specialising `φ` to the canonical isomorphism (whose construction
requires irreducibility of `POLY_GF2` over `ZMod 2`, i.e. a finite-
field development we omit here) recovers the GF(2¹⁶) interpretation
of the result. -/
@[step]
theorem mul2_spec (a b1 b2 : Std.U16) :
    mul2 a b1 b2 ⦃ result =>
      result.1.val.toGF216 = a.val.toGF216 * b1.val.toGF216 ∧
      result.2.val.toGF216 = a.val.toGF216 * b2.val.toGF216 ⦄ := by
  unfold mul2
  have h1 := mul_spec a b1
  have h2 := mul_spec a b2
  step*

end spqr.encoding.gf.unaccelerated
