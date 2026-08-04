/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import Spqr.Specs.Aeneas.SliceIteratorNext

/-!
# Spec theorem for `Enumerate<Iter<'_, T>>::next`

`Enumerate<Iter<'_, T>>` is the iterator produced by `slice.iter().enumerate()`.  Its `next`
method delegates to the inner slice iterator and pairs the yielded element with the running
counter:

  * If the inner cursor `i` is within bounds (`i < slice.len()`), it yields
    `Some((count, slice[i]))`, advances the cursor to `i + 1` and increments `count`
    (the increment is a checked `usize` addition, hence the `count + 1 ≤ usize::MAX`
    precondition).
  * Otherwise it yields `None` and leaves the iterator unchanged.

This is the composition `IteratorEnumerate.next (IteratorSliceIter T)` that appears at the head
of every extracted `enumerate`-loop body.  Registering the spec with `@[step]` lets the `step`
tactic discharge the iterator call in loop-body proofs directly, replacing the per-file
`*_next_post` helper lemmas and the manual `obtain ⟨…, hnext⟩ … rw [hnext]; simp only
[bind_tc_ok]` pattern.

**Source**: core/src/iter/adapters/enumerate.rs (Iterator impl for Enumerate)
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.core.iter.adapters.enumerate.IteratorEnumerate

/-- Checked `usize` increment always succeeds below `Usize.max` (existential form). -/
private lemma usize_add_one_ok (x : Usize) (h : x.val + 1 ≤ Usize.max) :
    ∃ (y : Usize), (x + 1#usize : Result Usize) = ok y ∧ y.val = x.val + 1 := by
  have h_add : x.val + (1#usize : Usize).val ≤ Usize.max := by scalar_tac
  have h_spec := Usize.add_spec h_add
  revert h_spec
  generalize (x + 1#usize : Result Usize) = res
  intro h_spec
  match res with
  | .ok z => exact ⟨z, rfl, by simp_all [WP.spec_ok]⟩
  | .fail e => simp_all
  | .div => simp_all

/--
**Spec theorem for `Enumerate<Iter<'_, T>>::next`** (WP form, `@[step]`):

Always succeeds and either:
  * yields `none` when the inner slice iterator is exhausted, leaving the iterator unchanged;
  * yields `some (count, slice[i])`, advancing the inner cursor and incrementing the counter.

**Source**: core/src/iter/adapters/enumerate.rs (Iterator impl for Enumerate)
-/
@[step]
theorem next_SliceIter_spec {T : Type}
    (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter T))
    (h_count : iter.iter.i < iter.iter.slice.length → iter.count.val + 1 ≤ Usize.max) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter T) iter
    ⦃ (opt, iter') =>
      match opt with
      | none =>
          ¬ iter.iter.i < iter.iter.slice.length ∧ iter' = iter
      | some iv =>
          ∃ (h : iter.iter.i < iter.iter.slice.length),
            iv.1 = iter.count ∧
            iv.2 = iter.iter.slice.val[iter.iter.i]'h ∧
            iter'.iter.slice = iter.iter.slice ∧
            iter'.iter.i = iter.iter.i + 1 ∧
            iter'.count.val = iter.count.val + 1 ⦄ := by
  simp only [core.iter.adapters.enumerate.IteratorEnumerate.next]
  obtain ⟨opt0, it', heq, h_none, h_some⟩ :=
    core.slice.iter.IteratorSliceIter.next_post iter.iter
  rw [heq]
  simp only [bind_tc_ok]
  by_cases hlt : iter.iter.i < iter.iter.slice.val.length
  · obtain ⟨hopt, hi, hslice⟩ := h_some hlt
    subst hopt
    have h_add : iter.count.val + 1 ≤ Usize.max := h_count hlt
    obtain ⟨count', hc_eq, hc_val⟩ := usize_add_one_ok iter.count h_add
    rw [hc_eq]
    simp only [bind_tc_ok, WP.spec_ok]
    exact ⟨hlt, rfl, rfl, hslice, hi, hc_val⟩
  · obtain ⟨hopt, hiter⟩ := h_none hlt
    subst hopt
    subst hiter
    simp only [WP.spec_ok]
    exact ⟨hlt, rfl⟩

end Aeneas.Std.core.iter.adapters.enumerate.IteratorEnumerate
