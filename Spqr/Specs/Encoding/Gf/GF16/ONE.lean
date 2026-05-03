/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf

/-! # Spec Theorem for `GF16::ONE`

Specification and proof for `encoding.gf.GF16.ONE`, the constant
representing the multiplicative identity (one element) of the Galois
field GF(2¹⁶).

In GF(2¹⁶) — the Galois field with 65 536 elements — the one element
is the unique element `1` satisfying `1 * a = a * 1 = a` for every
`a ∈ GF(2¹⁶)`.  Concretely, since GF16 is a transparent newtype
around `u16`, the one element is represented by the `u16` value `1`:
  `ONE = GF16 { value := 1_u16 }`

The underlying `u16` value `1` has natural-number value `1`, and lifts
into `GF216 = GaloisField 2 16` via the canonical chain
`Nat → (ZMod 2)[X] → GF216` (i.e. `Nat.toGF216 = φ ∘ natToGF2Poly`)
to the multiplicative identity `1 : GF216`.  This follows because:
  * `natToGF2Poly 1 = 1` (the bit pattern `0b1` represents the
    constant polynomial `1` in `(ZMod 2)[X]`); and
  * the ring homomorphism `φ : (ZMod 2)[X] →+* GF216` chosen in
    `Spqr.Math.Gf` preserves one (`map_one`).

**Source**: spqr/src/encoding/gf.rs (lines 542:4-542:44)
-/

open Aeneas Aeneas.Std Result
open spqr.encoding.gf.unaccelerated

namespace spqr.encoding.gf.GF16

/-
natural language description:

• `ONE` is the public associated constant on the `GF16` struct.
• It is defined as `GF16 { value: 1_u16 }`, i.e. the unique
  `GF16` whose underlying `u16` representation is `1`.
• The constant is unconditional and pure — its evaluation never
  fails and never depends on any input.

natural language specs:

• The underlying `u16` value of `ONE` is `1`:
    `ONE.value = 1#u16`
  and equivalently as a natural number:
    `ONE.value.val = 1`.
• Lifting `ONE.value.val` into `GF216` via the canonical map
  `Nat.toGF216 = φ ∘ natToGF2Poly` yields the multiplicative identity
  of `GF216 = GaloisField 2 16`:
    `(ONE.value.val.toGF216 : GF216) = 1`.
• `ONE` is a left- and right-identity for `GF16` multiplication: for
  every `a : GF16`, `a * ONE` and `ONE * a` lift to `a.value.val.toGF216`
  in `GF216`, which follows from the GF(2¹⁶) identity `x * 1 = x`.
-/

/-- **The underlying `u16` of `ONE` is `1_u16`**. -/
@[simp]
theorem ONE_value : (ONE).value = 1#u16 := by
  simp [ONE]

/-- **The underlying natural-number value of `ONE` is `1`**. -/
@[simp]
theorem ONE_value_val : (ONE).value.val = 1 := by
  simp [ONE]

/-- **`natToGF2Poly 1 = 1`**: the binary representation of the natural
number `1` is the single-bit pattern `0b1`, which encodes the constant
polynomial `1` over `(ZMod 2)`. -/
private lemma natToGF2Poly_one : natToGF2Poly 1 = 1 := by
  unfold natToGF2Poly
  simp

/-- **Spec and proof concerning `encoding.gf.GF16.ONE`**:

`ONE` is the multiplicative identity of GF(2¹⁶): lifting its
underlying `u16` representation into `GF216 = GaloisField 2 16` via
the canonical map `Nat.toGF216 n = φ (natToGF2Poly n)` gives the
one element of `GF216`.

Concretely:

  `(ONE.value.val.toGF216 : GF216) = 1`

The proof unfolds `ONE` to expose the underlying `u16` value `1`,
reduces `(1 : Std.U16).val` to `1 : Nat`, and then computes
`Nat.toGF216 1 = φ (natToGF2Poly 1) = φ 1 = 1` using
`natToGF2Poly_one` together with the ring-homomorphism law
`map_one`.

**Source**: spqr/src/encoding/gf.rs (lines 542:4-542:44)
-/
@[simp]
theorem ONE_toGF216 : (ONE.value.val.toGF216 : GF216) = 1 := by
  simp [Nat.toGF216, natToGF2Poly_one]

/-- **Top-level spec for `encoding.gf.GF16.ONE`** (Hoare-triple form):

Reading the constant `encoding.gf.GF16.ONE` (lifted into the `Result`
monad as a pure value) yields a `GF16` whose underlying `u16`
representation lifts to the multiplicative identity of
`GF216 = GaloisField 2 16` via the canonical map
`Nat.toGF216 = φ ∘ natToGF2Poly`:

  `ok ONE ⦃ result => (result.value.val.toGF216 : GF216) = 1 ⦄`

The proof discharges the trivial Hoare triple by reducing
`ok ONE` and applying `ONE_toGF216`, which combines
`natToGF2Poly_one` with the ring-homomorphism law `map_one`
for the chosen `φ : (ZMod 2)[X] →+* GF216`.

**Source**: spqr/src/encoding/gf.rs (lines 542:4-542:44)
-/
@[step]
theorem one_spec :
    ok ONE ⦃ result =>
      (result.value.val.toGF216 : GF216) = 1 ⦄ := by
  simp [Nat.toGF216, natToGF2Poly_one]

end spqr.encoding.gf.GF16
