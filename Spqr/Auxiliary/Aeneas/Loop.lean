/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import Aeneas
public import Spqr.Auxiliary.Aeneas.Result

/-! # Staged for upstream to Aeneas `Std/Primitives.lean`

Partial correctness of `loop` in the "if it returns `Ok`" form. Unlike `loop.spec`, it needs
no proof that the body succeeds. -/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Aeneas.Std

/-- Assume that every successful step from a state that satisfies `inv` either finishes with a
value that satisfies `post`, or continues to a state that satisfies `inv` with a smaller
`measure`. Then a successful `loop` from a state that satisfies `inv` returns a value that
satisfies `post`. -/
theorem loop_ok_post {α β : Type} (measure : α → Nat) (inv : α → Prop) (post : β → Prop)
    (body : α → Result (ControlFlow α β))
    (hBody : ∀ x r, inv x → body x = ok r → match r with
      | .done y => post y
      | .cont x' => inv x' ∧ measure x' < measure x) :
    ∀ x y, inv x → loop body x = ok y → post y := by
  intro x
  induction hm : measure x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    intro y hi h
    rw [loop] at h
    obtain ⟨r, hr, h⟩ := Result.bind_eq_ok.mp h
    have hb := hBody x r hi hr
    cases r with
    | done z => simp only [ok.injEq] at h; subst h; exact hb
    | cont x' => exact ih (measure x') (hm ▸ hb.2) x' rfl y hb.1 h

end Aeneas.Std
