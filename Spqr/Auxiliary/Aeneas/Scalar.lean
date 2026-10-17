/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
module

public import Aeneas


/-! # Staged for upstream to Aeneas `Std/Scalar/`

Aeneas scalars and their Lean core counterparts are both `BitVec` wrappers. This provides conversion
between them. Only `U8`/`UInt8` is provided since that is all that is currently required.

It also reads the value off a checked addition that returned `ok`, and the value of a `u16` off its
big-endian byte pair. -/

@[expose] public section

namespace Aeneas.Std

open Function

/-- An Aeneas byte as a core `UInt8`. -/
def U8.toUInt8 (x : U8) : UInt8 := ⟨x.bv⟩

/-- A core `UInt8` as an Aeneas byte. -/
def U8.ofUInt8 (y : UInt8) : U8 := ⟨y.toBitVec⟩

@[simp, grind =]
theorem U8.ofUInt8_toUInt8 (x : U8) : U8.ofUInt8 x.toUInt8 = x := rfl

@[simp, grind =]
theorem U8.toUInt8_ofUInt8 (y : UInt8) : (U8.ofUInt8 y).toUInt8 = y := rfl

@[simp, grind =]
theorem U8.toNat_toUInt8 (x : U8) : x.toUInt8.toNat = x.val := rfl

@[simp, grind =]
theorem U8.map_ofUInt8_map_toUInt8 (l : List U8) :
    List.map (U8.ofUInt8 ∘ U8.toUInt8) l = l := by simp [comp_def]

@[simp, grind =]
theorem U8.map_toUInt8_map_ofUInt8 (l : List UInt8) :
    List.map (U8.toUInt8 ∘ U8.ofUInt8) l = l := by simp [comp_def]

theorem UScalar.val_of_add_eq_ok {ty : UScalarTy} {x y z : UScalar ty} (h : x + y = Result.ok z) :
    z.val = x.val + y.val := by
  have := UScalar.add_equiv x y
  rw [h] at this
  exact this.2.1

/-- **Big-endian byte pair of a `u16`**: if the two big-endian bytes of `x` are `[b0, b1]`, then
`256 * b0.val + b1.val = x.val`. -/
theorem U16.toBEBytes_pair_val (x : U16) (b0 b1 : U8)
    (h : [b0, b1] = List.map (UScalar.mk (ty := .U8)) x.bv.toBEBytes) :
    256 * b0.val + b1.val = x.val := by
  have h0 : b0 = (List.map (UScalar.mk (ty := .U8)) x.bv.toBEBytes)[0]! := by rw [← h]; simp
  have h1 : b1 = (List.map (UScalar.mk (ty := .U8)) x.bv.toBEBytes)[1]! := by rw [← h]; simp
  subst h0 h1
  simp only [Std.UScalar.val]
  simp [BitVec.toBEBytes, BitVec.toLEBytes, Nat.shiftRight_eq_div_pow]
  grind

end Aeneas.Std
