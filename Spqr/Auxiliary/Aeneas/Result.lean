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

theorem core.result.Result.Insts.CoreOpsTry.branch_eq_continue {T E : Type}
    {r : core.result.Result T E} {v : T}
    (h : core.result.Result.Insts.CoreOpsTry.branch r = Result.ok (.Continue v)) :
    r = .Ok v := by
  cases r <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch]

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
