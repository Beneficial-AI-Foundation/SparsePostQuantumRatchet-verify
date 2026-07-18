/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import Aeneas

/-!
# Staged for upstream to Aeneas `Std/Slice.lean` -/
-- https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/305

open Aeneas Aeneas.Std

/-- Constructs an `Aeneas.Std.Slice` from a `List`, discharging the `length ≤ Usize.max` obligation
with grind by default. -/
def _root_.Aeneas.Std.Slice.make {α : Type} (l : List α) (h : l.length ≤ Usize.max := by grind) :
    Slice α := ⟨l, h⟩

@[simp, grind =] theorem _root_.Aeneas.Std.Slice.val_make {α : Type} (l : List α) (h) :
    (Slice.make l h).val = l := rfl

-- Not `@[simp]`: `Slice.length` is reducibly `·.val.length`, so `simp` already normalizes
-- `(Slice.make l h).length` via `val_make` (flagged by the `simpNF` linter otherwise).
@[scalar_tac_simps, grind =] theorem _root_.Aeneas.Std.Slice.length_make {α : Type}
    (l : List α) (h) : (Slice.make l h).length = l.length := rfl

@[simp, grind =] theorem _root_.Aeneas.Std.Slice.make_val {α : Type} (s : Slice α) (h) :
    Slice.make s.val h = s := rfl

theorem _root_.Aeneas.Std.Slice.make_inj {α : Type} (l₁ l₂ : List α) (h₁ h₂) :
    Slice.make l₁ h₁ = Slice.make l₂ h₂ ↔ l₁ = l₂ :=
  Subtype.ext_iff
