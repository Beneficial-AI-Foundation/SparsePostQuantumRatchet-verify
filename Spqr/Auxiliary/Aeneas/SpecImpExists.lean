/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
module

public import Aeneas


/-!
# Inversion lemmas for `spec` on `Result`

Aeneas removed `spec_imp_exists` / `exists_imp_spec` in `nightly-2026.10.07` (aeneas#1384) in
favour of compositional reasoning with `spec_bind`, `spec_mono`, `spec_and` and `spec_exists`.
They are still true for the current `Result` model: its only effect, `fail`, never resumes, and
`spec_vis`/`spec_div` rule out failure and divergence.  This file re-proves them so existing
proofs keep working while they are migrated to the compositional style.

It also provides `bind_spec_true`, the inversion of a *no-panic* spec on a `bind`: it recovers
the value returned by the head and the no-panic spec of the tail.  This is the tool used by
spec theorems that take a non-panic hypothesis on a whole function (e.g. `spqr.recv_spec`) and
need to peel it off one `?`/`let ←` at a time.  Unlike `spec_bind`, it works backwards from an
assumed spec rather than forwards from the sub-call specs.
-/

@[expose] public section

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

/-- A non-panicking `bind` has a non-panicking head, and its tail does not panic on the value
the head returns. -/
theorem bind_spec_true {α β : Type} {m : Result α} {k : α → Result β}
    (h : (Std.bind m k) ⦃ _ => True ⦄) :
    ∃ v, m = ok v ∧ (k v) ⦃ _ => True ⦄ := by
  cases hm : m with
  | ret v => exact ⟨v, rfl, by rw [hm, bind_ok] at h; exact h⟩
  | vis _ _ => rw [hm, bind_vis] at h; exact (spec_vis _ _).mp h |>.elim
  | div => rw [hm, bind_div] at h; exact spec_div.mp h |>.elim

end Aeneas.Std.WP
