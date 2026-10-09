/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import Aeneas

/-!
# `spec_imp_exists` / `exists_imp_spec` (removed upstream)

Aeneas removed these in `nightly-2026.10.07` (aeneas#1384) in favour of compositional reasoning
with `spec_bind`, `spec_mono`, `spec_and` and `spec_exists`. They are still true for the current
`Result` model: its only effect, `fail`, never resumes, and `spec_vis`/`spec_div` rule out failure
and divergence. This file re-proves them so existing proofs keep working while they are migrated
to the compositional style.
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.WP

/-- A spec guarantees the computation returns some value satisfying the postcondition. -/
theorem spec_imp_exists {α : Type} {m : Result α} {p : Post α} (h : spec m p) :
    ∃ v, m = ok v ∧ p v := by
  cases m with
  | ret v => exact ⟨v, rfl, (spec_ok v).mp h⟩
  | vis e k => exact ((spec_vis e k).mp h).elim
  | div => exact (spec_div.mp h).elim

/-- Converse of `spec_imp_exists`. -/
theorem exists_imp_spec {α : Type} {m : Result α} {p : Post α} (h : ∃ v, m = ok v ∧ p v) :
    spec m p := by
  obtain ⟨v, rfl, hv⟩ := h
  exact (spec_ok v).mpr hv

end Aeneas.Std.WP
