/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import Aeneas

/-!
# Reflexive spec strengthening (staged for upstream to the Aeneas WP layer)

`spec_refl` strengthens any spec's postcondition with the call identity `m = ok r`. The `refl_of%`
elaborator lifts this over the binders of a `∀`-quantified spec theorem, so a reflexive spec can be
dropped into a proof's local context.
-/
-- https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/305

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Aeneas.Std.WP

/-- Strengthen any spec's postcondition with the identity `m = ok r`. -/
theorem spec_refl {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) :
    m ⦃ fun r => P r ∧ m = ok r ⦄ := by
  obtain ⟨r, h_eq, h_post⟩ := spec_imp_exists h
  exact exists_imp_spec ⟨r, h_eq, h_post, h_eq⟩

open Lean Elab Term Meta in
/-- `refl_of% e` turns a spec theorem `e` of the form `∀ xs, m xs ⦃ P xs ⦄` into its strengthening
`∀ xs, m xs ⦃ fun r => P xs r ∧ m xs = ok r ⦄`, telescoping the binders and applying `spec_refl`
under them. Any arity (including none). Errors if `e` is not, after telescoping, a spec. -/
elab "refl_of% " t:term : term => withRef t do
  let e ← elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars (← inferType e)
  forallTelescope ty fun xs body => do
    let refled ←
      try mkAppM ``spec_refl #[mkAppN e xs]
      catch _ =>
        throwError "refl_of%: expected a spec `m ⦃ P ⦄`, but the statement concludes \
          with{indentExpr body}"
    mkLambdaFVars xs refled

end Aeneas.Std.WP
