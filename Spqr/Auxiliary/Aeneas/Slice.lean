/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import Aeneas

/-!
# `Slice` helpers (staged for upstream to Aeneas `Std/Slice.lean`)

`Slice.make`, a smart constructor for a `Slice` from a list, discharging the length obligation with
`grind` by default, together with the projection/injectivity simp lemmas that let `simp` see through
it.
-/

open Aeneas Aeneas.Std

-- TODO: upstream to Aeneas (`Std/Slice.lean`).
/-- Make a `Aeneas.Std.Slice` from a `List`, attempt to prove the length requirement. -/
def _root_.Aeneas.Std.Slice.make {α : Type} (l : List α) (h : l.length ≤ Usize.max := by grind) :
    Slice α := ⟨l, h⟩

@[simp] theorem _root_.Aeneas.Std.Slice.val_make {α : Type} (l : List α) (h) :
    (Slice.make l h).val = l := rfl

@[simp] theorem _root_.Aeneas.Std.Slice.length_make {α : Type} (l : List α) (h) :
    (Slice.make l h).length = l.length := rfl

@[simp] theorem _root_.Aeneas.Std.Slice.make_val {α : Type} (s : Slice α) (h) :
    Slice.make s.val h = s := rfl

theorem _root_.Aeneas.Std.Slice.make_inj {α : Type} (l₁ l₂ : List α) (h₁ h₂) :
    Slice.make l₁ h₁ = Slice.make l₂ h₂ ↔ l₁ = l₂ :=
  Subtype.ext_iff
