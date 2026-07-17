/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import Aeneas

/-! # Staged for upstream to Aeneas `Std/Array/Array.lean` -/

open Aeneas Aeneas.Std

@[simp, grind =] theorem _root_.Aeneas.Std.Array.val_make {α : Type}
    (n : Usize) (l : List α) (h) : (Array.make n l h).val = l := rfl

@[scalar_tac(Array.make n l h), grind =] theorem _root_.Aeneas.Std.Array.length_make {α : Type}
    (n : Usize) (l : List α) (h) : (Array.make n l h).length = n.val := h

@[simp, grind =] theorem _root_.Aeneas.Std.Array.make_val {α : Type} {n : Usize} (a : Array α n)
    (h) : Array.make n a.val h = a := rfl

theorem _root_.Aeneas.Std.Array.make_inj {α : Type} {n : Usize} (l₁ l₂ : List α) (h₁ h₂) :
    Array.make n l₁ h₁ = Array.make n l₂ h₂ ↔ l₁ = l₂ :=
  Subtype.ext_iff
