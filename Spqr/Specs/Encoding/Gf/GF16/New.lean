/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf

/-! # Spec Theorem for `GF16::new`

Specification and proof for `encoding.gf.GF16.new`, the public
constructor that lifts a raw `u16` value into a `GF16` field element
of the Galois field GF(2¹⁶).

In GF(2¹⁶) — the Galois field with 65 536 elements — every element
is represented internally by a 16-bit unsigned integer.  The `new`
function is the trivial wrapper that takes a `u16` value and packages
it as a `GF16`:
  `new value = ok (GF16 { value })`

The constructor is unconditional and pure — it never fails and
performs no arithmetic on its input.  Conceptually, it implements
the canonical bijection between the raw representation `u16` and
the abstract type `GF16`, and so its semantic interpretation in
`GF216 = GaloisField 2 16` is exactly the lift of the input `u16`
under the canonical map
`Nat.toGF216 = φ ∘ natToGF2Poly` (with
`φ : (ZMod 2)[X] →+* GF216`).

**Source**: spqr/src/encoding/gf.rs (lines 544:4-546:5)
-/

open Aeneas Aeneas.Std Result
open spqr.encoding.gf.unaccelerated

namespace spqr.encoding.gf.GF16

/-
natural language description:

• Takes a single `u16` argument `value` representing the raw bit
  pattern of an element of GF(2¹⁶).
• Returns the `GF16` field element `GF16 { value }` whose underlying
  `u16` is exactly the input, lifted into the `Result` monad as
  `ok (GF16 { value })`.
• The constructor is unconditional and pure — its evaluation never
  fails and never depends on any state beyond its input.

natural language specs:

• The function always succeeds: `new value = ok (GF16 { value })`.
• The underlying `u16` value of the wrapped `GF16` is `value`, and
  equivalently as a natural number it is `value.val`.
• Lifting `value.val` into `GF216` via the canonical map
  `Nat.toGF216 = φ ∘ natToGF2Poly` yields the GF(2¹⁶) element
  represented by the raw input `value`:
    `(value.val.toGF216 : GF216) = value.val.toGF216`.
  In Hoare-triple form, calling `new value` produces a `GF16`
  `result` whose lift agrees with that of the raw input:
    `new value ⦃ result =>
        (result.value.val.toGF216 : GF216) = value.val.toGF216 ⦄`.
-/

/-- **`new value` reduces to `ok (GF16 { value })`**: the constructor
is the trivial monadic wrapper around the underlying `u16`. -/
@[simp]
theorem new_eq (value : Std.U16) :
    new value = ok ({ value } : spqr.encoding.gf.GF16) := by
  simp [new]

/-- **Spec and proof concerning `encoding.gf.GF16.new`**:

`new` is the trivial constructor of `GF16`: it wraps a `u16` value
into the transparent newtype, so the underlying `u16` of the
resulting `GF16` is exactly the input `value`, and lifting it into
`GF216 = GaloisField 2 16` via the canonical map
`Nat.toGF216 n = φ (natToGF2Poly n)` agrees with directly lifting
the raw input `value.val`.

Concretely (extracting the `GF16` from the `ok`-wrapped result):

  `((GF16.mk value).value.val.toGF216 : GF216) = value.val.toGF216`

The proof reduces `(GF16.mk value).value` to `value` definitionally
and closes the resulting trivial equality.

**Source**: spqr/src/encoding/gf.rs (lines 544:4-546:5)
-/
@[simp]
theorem mk_value_toGF216 (value : Std.U16) :
    (({ value } : spqr.encoding.gf.GF16).value.val.toGF216 : GF216)
      = value.val.toGF216 := by
  rfl

/-- **Top-level spec for `encoding.gf.GF16.new`** (Hoare-triple form):

Calling the constructor `encoding.gf.GF16.new value` (lifted into the
`Result` monad) yields a `GF16` whose underlying `u16` representation
lifts to the same element of `GF216 = GaloisField 2 16` as the raw
input `value`, via the canonical map
`Nat.toGF216 = φ ∘ natToGF2Poly`:

  `new value ⦃ result =>
       (result.value.val.toGF216 : GF216) = value.val.toGF216 ⦄`

The proof discharges the trivial Hoare triple by reducing
`new value` to `ok (GF16 { value })` (via `new_eq`) and noting that
the underlying `u16` of the resulting `GF16` is definitionally
`value`, so its `Nat.toGF216` lift is `value.val.toGF216`.

**Source**: spqr/src/encoding/gf.rs (lines 544:4-546:5)
-/
@[step]
theorem new_spec (value : Std.U16) :
    new value ⦃ result =>
      (result.value.val.toGF216 : GF216) = value.val.toGF216 ⦄ := by
  simp [new]

end spqr.encoding.gf.GF16
