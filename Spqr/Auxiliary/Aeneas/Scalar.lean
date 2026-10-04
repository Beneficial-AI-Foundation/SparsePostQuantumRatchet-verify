/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import Aeneas

/-! # Staged for upstream to Aeneas `Std/Scalar/`

Aeneas scalars and their Lean core counterparts are both `BitVec` wrappers. This provides conversion
between them. Only `U8`/`UInt8` is provided since that is all that is currently required. -/

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

end Aeneas.Std
