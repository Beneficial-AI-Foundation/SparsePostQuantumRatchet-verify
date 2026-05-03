/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf

/-! # Spec Theorem for `GF16::ZERO`

Specification and proof for `encoding.gf.GF16.ZERO`, the constant
representing the additive identity (zero element) of the Galois
field GF(2¹⁶).

In GF(2¹⁶) — the Galois field with 65 536 elements — the zero element
is the unique element `0` satisfying `0 + a = a + 0 = a` for every
`a ∈ GF(2¹⁶)`.  Concretely, since GF16 is a transparent newtype
around `u16` whose addition is bitwise XOR, the zero element is
represented by the `u16` value `0`:
  `ZERO = GF16 { value := 0_u16 }`

The underlying `u16` value `0` has natural-number value `0`, and lifts
into `GF216 = GaloisField 2 16` via the canonical chain
`Nat → (ZMod 2)[X] → GF216` (i.e. `Nat.toGF216 = φ ∘ natToGF2Poly`)
to the additive identity `0 : GF216`.  This follows because:
  * `natToGF2Poly 0 = 0` (the empty bit pattern represents the zero
    polynomial in `(ZMod 2)[X]`); and
  * the ring homomorphism `φ : (ZMod 2)[X] →+* GF216` chosen in
    `Spqr.Math.Gf` preserves zero (`map_zero`).

**Source**: spqr/src/encoding/gf.rs (lines 541:4-541:45)
-/

open Aeneas Aeneas.Std Result
open spqr.encoding.gf.unaccelerated

namespace spqr.encoding.gf.GF16

/-
natural language description:

• `ZERO` is the public associated constant on the `GF16` struct.
• It is defined as `GF16 { value: 0_u16 }`, i.e. the unique
  `GF16` whose underlying `u16` representation is `0`.
• The constant is unconditional and pure — its evaluation never
  fails and never depends on any input.

natural language specs:

• The underlying `u16` value of `ZERO` is `0`:
    `ZERO.value = 0#u16`
  and equivalently as a natural number:
    `ZERO.value.val = 0`.
• Lifting `ZERO.value.val` into `GF216` via the canonical map
  `Nat.toGF216 = φ ∘ natToGF2Poly` yields the additive identity of
  `GF216 = GaloisField 2 16`:
    `(ZERO.value.val.toGF216 : GF216) = 0`.
• `ZERO` is a left- and right-identity for `GF16` addition (which is
  bitwise XOR): for every `a : GF16`,
    `(a + ZERO).value.val.toGF216 = a.value.val.toGF216`,
  which follows from the GF(2¹⁶) identity `x + 0 = x`.
-/

/-- **The underlying `u16` of `ZERO` is `0_u16`**. -/
@[simp]
theorem ZERO_value : (ZERO).value = 0#u16 := by
  simp [ZERO]

/-- **The underlying natural-number value of `ZERO` is `0`**. -/
@[simp]
theorem ZERO_value_val : (ZERO).value.val = 0 := by
  simp [ZERO]

/-- **Spec and proof concerning `encoding.gf.GF16.ZERO`**:

`ZERO` is the additive identity of GF(2¹⁶): lifting its underlying
`u16` representation into `GF216 = GaloisField 2 16` via the
canonical map `Nat.toGF216 n = φ (natToGF2Poly n)` gives the
zero element of `GF216`.

Concretely:

  `(ZERO.value.val.toGF216 : GF216) = 0`

The proof unfolds `ZERO` to expose the underlying `u16` value `0`,
reduces `(0 : Std.U16).val` to `0 : Nat`, and then computes
`Nat.toGF216 0 = φ (natToGF2Poly 0) = φ 0 = 0` using
`natToGF2Poly_zero` together with the ring-homomorphism law
`map_zero`.

**Source**: spqr/src/encoding/gf.rs (lines 541:4-541:45)
-/
@[simp]
theorem ZERO_toGF216 : (ZERO.value.val.toGF216 : GF216) = 0 := by
  simp [Nat.toGF216, natToGF2Poly_zero]

/-- **Top-level spec for `encoding.gf.GF16.ZERO`** (Hoare-triple form):

Reading the constant `encoding.gf.GF16.ZERO` (lifted into the `Result`
monad as a pure value) yields a `GF16` whose underlying `u16`
representation lifts to the additive identity of
`GF216 = GaloisField 2 16` via the canonical map
`Nat.toGF216 = φ ∘ natToGF2Poly`:

  `ok ZERO ⦃ result => (result.value.val.toGF216 : GF216) = 0 ⦄`

The proof discharges the trivial Hoare triple by reducing
`ok ZERO` and applying `ZERO_toGF216`, which combines
`natToGF2Poly_zero` with the ring-homomorphism law `map_zero`
for the chosen `φ : (ZMod 2)[X] →+* GF216`.

**Source**: spqr/src/encoding/gf.rs (lines 541:4-541:45)
-/
@[step]
theorem zero_spec :
    ok ZERO ⦃ result =>
      (result.value.val.toGF216 : GF216) = 0 ⦄ := by
  simp [Nat.toGF216, natToGF2Poly_zero]

end spqr.encoding.gf.GF16
