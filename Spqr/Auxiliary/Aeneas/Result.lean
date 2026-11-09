/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import Aeneas

/-! # Staged for upstream to Aeneas `Std/Primitives.lean` and `Std/Core/Convert.lean`

Inversion lemmas for proofs in the "if it returns `Ok`" form: a bind that returns `ok`, and
the two halves of the Rust `?` operator, `Result::branch` and `Result::from_residual`; plus
`WP.spec_bind_ok` for stepping over `ok x >>= f` when `simp [bind_ok]` cannot. -/

@[expose] public section

namespace Aeneas.Std

theorem Result.bind_eq_ok {α β : Type} {x : Result α} {f : α → Result β} {y : β} :
    bind x f = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp

/-- A spec for `ok x >>= f` follows from a spec for `f x`. -/
theorem WP.spec_bind_ok {α β : Type} {x : α} {f : α → Result β} {P : WP.Post β}
    (h : WP.spec (f x) P) : WP.spec (bind (Result.ok x) f) P :=
  WP.spec_bind (Pₘ := (· = x)) ((WP.spec_ok x).mpr rfl) (by rintro _ rfl; exact h)

end Aeneas.Std

open Aeneas.Std

/-- Equation for `Result::branch` on an `Ok`. -/
@[simp]
theorem core.result.Result.Insts.CoreOpsTry.branch_Ok {T E : Type} (v : T) :
    core.result.Result.Insts.CoreOpsTry.branch (E := E) (.Ok v) = Result.ok (.Continue v) :=
  rfl

/-- Equation for `Result::branch` on an `Err`. -/
@[simp]
theorem core.result.Result.Insts.CoreOpsTry.branch_Err {T E : Type} (e : E) :
    core.result.Result.Insts.CoreOpsTry.branch (T := T) (.Err e) =
      Result.ok (.Break (.Err e)) :=
  rfl

/-- Equation for `Result::from_residual` with the identity `From` instance: the error is
propagated unchanged. -/
@[simp]
theorem core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual_same
    {T E : Type} (e : E) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      T (core.convert.FromSame E) (.Err e) = Result.ok (.Err e) := by
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Inversion of `from_residual_same`: if the `Break` arm of a `?` (with the identity `From`
instance) returns `r`, then `r` is the propagated error. -/
theorem core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual_same_eq_ok
    {T E : Type} {e : E} {r : core.result.Result T E}
    (h : core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      T (core.convert.FromSame E) (.Err e) = Result.ok r) :
    r = .Err e := by
  rw [from_residual_same, Result.ok.injEq] at h
  exact h.symm

theorem core.result.Result.Insts.CoreOpsTry.branch_eq_continue {T E : Type}
    {r : core.result.Result T E} {v : T}
    (h : core.result.Result.Insts.CoreOpsTry.branch r = Result.ok (.Continue v)) :
    r = .Ok v := by
  cases r <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch]

theorem core.result.Result.Insts.CoreOpsTry.branch_eq_break {T E : Type}
    {r : core.result.Result T E} {res : core.result.Result Never E}
    (h : core.result.Result.Insts.CoreOpsTry.branch r = Result.ok (.Break res)) :
    ∃ e, r = .Err e ∧ res = .Err e := by
  cases r with
  | Ok v => simp [core.result.Result.Insts.CoreOpsTry.branch] at h
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq,
      core.ops.control_flow.ControlFlow.Break.injEq] at h
    exact ⟨e, rfl, h.symm⟩

/-- The `Break` arm of a `?` never returns `Ok`. -/
theorem core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual_ne_ok
    {T E F : Type} {inst : core.convert.From F E}
    {r : core.result.Result Never E} {x : T} :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      T inst r ≠ Result.ok (.Ok x) := by
  intro h
  cases r with
  | Ok v => cases v
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    cases hf : inst.from e <;> simp_all [Bind.bind]

/-- If `branch r` returns `cf`, `f cf` returns `Ok x`, and `f` maps every `Break res` to
`from_residual res`, then `r` is `Ok v` for some `v`, and `f (Continue v)` returns `Ok x`. -/
theorem core.result.Result.Insts.CoreOpsTry.continue_of_ok {T E F U : Type}
    {inst : core.convert.From F E} {r : core.result.Result T E}
    {f : core.ops.control_flow.ControlFlow (core.result.Result Never E) T →
      Result (core.result.Result U F)} {x : U}
    (h : ∃ cf, core.result.Result.Insts.CoreOpsTry.branch r = Result.ok cf ∧
      f cf = Result.ok (.Ok x))
    (hb : ∀ res, f (.Break res) =
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual U inst res) :
    ∃ v, r = .Ok v ∧ f (.Continue v) = Result.ok (.Ok x) := by
  obtain ⟨cf, hcf, h⟩ := h
  cases cf with
  | Continue v => exact ⟨v, branch_eq_continue hcf, h⟩
  | Break res =>
    rw [hb] at h
    exact (core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual_ne_ok h).elim
