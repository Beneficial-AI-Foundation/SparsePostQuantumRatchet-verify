/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import Aeneas

/-! # Membership in Aeneas arrays -/

@[expose] public section

open Aeneas Aeneas.Std

namespace Aeneas.Std.Array

/-- If every entry of `a`, read with `a[j]!`, satisfies `P`, then every member of `a` does. -/
theorem forall_mem_of_forall_lt {α : Type} [Inhabited α] {n : Usize} {a : Array α n}
    {P : α → Prop} (h : ∀ j < n.val, P a[j]!) : ∀ x ∈ a.val, P x := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hj' : j < n.val := by have := a.property; omega
  have := h j hj'
  rwa [Array.getElem!_Nat_eq, getElem!_pos a.val j hj] at this

end Aeneas.Std.Array
