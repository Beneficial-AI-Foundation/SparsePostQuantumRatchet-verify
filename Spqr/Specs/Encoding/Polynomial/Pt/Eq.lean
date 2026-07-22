/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-! # Spec Theorem for `Pt::eq` (PartialEq / Eq)

Compares only x-coordinates: `eq(a, b) = (a.x.value == b.x.value)`, ignoring y.
Consistent with `PartialOrd`/`Ord`.

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial.Pt

/-- **Spec theorem for `encoding.polynomial.Pt.Insts.CoreCmpPartialEqPt.eq`**:

Always succeeds; returns `true` iff `self.x.value = other.x.value` (y ignored). -/
@[step]
theorem eq_spec (self other : spqr.encoding.polynomial.Pt) :
    Insts.CoreCmpPartialEqPt.eq self other ⦃ (result : Bool) =>
      result = true ↔ self.x.value = other.x.value ⦄ := by
  simp [Insts.CoreCmpPartialEqPt.eq]

/-- Structural equality: `a = b ↔ a.x = b.x ∧ a.y = b.y` (strictly finer than `PartialEq`). -/
theorem pt_eq_iff (a b : spqr.encoding.polynomial.Pt) :
    a = b ↔ a.x = b.x ∧ a.y = b.y := by
  constructor
  · intro h; rw [h]; exact ⟨rfl, rfl⟩
  · intro ⟨hx, hy⟩
    cases a
    cases b
    simp only at hx hy
    subst hx
    subst hy
    rfl

end spqr.encoding.polynomial.Pt
