/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `core::iter::range::{Iterator for Range<A>}::step_by`

`Iterator::step_by(step)` on a range simply wraps the range and the step into a
`StepBy` adapter, panicking iff `step = 0`.  The Aeneas-extracted
`core.iter.range.IteratorRange.step_by` mirrors this:
`if step.val = 0 then fail .panic else ok ⟨range, step⟩`.

The spec theorem lets the `step` tactic walk through `step_by` calls (e.g. Rust's
`for i in (a..b).step_by(n)`) instead of stopping at them.

**Source**: core/src/iter/traits/iterator.rs (`Iterator::step_by`)
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.core.iter.range.IteratorRange

/-- **Spec theorem for `core.iter.range.IteratorRange.step_by`**:

For a non-zero step, `step_by` succeeds and returns the `StepBy` adapter wrapping
exactly the input range and step. -/
@[step]
theorem step_by_spec {A : Type} (StepInst : core.iter.range.Step A)
    (range : core.ops.range.Range A) (step : Usize) (h : step.val ≠ 0) :
    core.iter.range.IteratorRange.step_by StepInst range step ⦃
      (it : core.iter.adapters.step_by.StepBy (core.ops.range.Range A)) =>
      it = { iter := range, step_by := step } ⦄ := by
  unfold core.iter.range.IteratorRange.step_by
  simp [WP.spec_ok, h]

end Aeneas.Std.core.iter.range.IteratorRange
