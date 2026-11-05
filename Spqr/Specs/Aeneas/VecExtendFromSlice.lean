/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
import Spqr.Auxiliary.Aeneas.SpecImpExists

/-!
# Spec theorems for `alloc::vec::Vec::extend_from_slice`

Specs for `extend_from_slice` when `Clone` is the identity (e.g. `U8`, `GF16`),
showing the result is `v ++ s`. Used in serialization proofs in `Spqr.Specs.Encoding.Polynomial`.-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.alloc.vec.Vec

/-- **Spec theorem for `alloc.vec.Vec.extend_from_slice` specialised to `U8`**:

Since `CloneU8.clone x = ok x`, the result is `v.val ++ s.val`
given `v.val.length + s.val.length ≤ Usize.max`. -/
@[step]
theorem extend_from_slice_U8_spec
    (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ (r : alloc.vec.Vec U8) =>
      r = v ++ s.val ⦄ := by
  have h_clone_x : ∀ x ∈ s.val, core.clone.CloneU8.clone x = ok x := by
    intros _ _; rfl
  unfold alloc.vec.Vec.extend_from_slice
  have hlen : v.length + s.length ≤ Usize.max := h
  rw [dite_eq_left hlen]
  step*

/-- **Spec theorem for `alloc.vec.Vec.extend_from_slice` specialised to `GF16`**:

Since `GF16.Clone.clone x = ok x`, the result is `v.val ++ s.val`
given `v.val.length + s.val.length ≤ Usize.max`. -/
@[step]
theorem extend_from_slice_GF16_spec
    (v : alloc.vec.Vec spqr.encoding.gf.GF16)
    (s : Slice spqr.encoding.gf.GF16)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice
      spqr.encoding.gf.GF16.Insts.CoreCloneClone v s ⦃ (r : alloc.vec.Vec spqr.encoding.gf.GF16) =>
      r = v ++ s.val ⦄ := by
  have h_clone_x : ∀ x ∈ s.val, spqr.encoding.gf.GF16.Insts.CoreCloneClone.clone x = ok x := by
    intros _ _
    simp [spqr.encoding.gf.GF16.Insts.CoreCloneClone.clone]
  unfold alloc.vec.Vec.extend_from_slice
  have hlen : v.length + s.length ≤ Usize.max := h
  rw [dite_eq_left hlen]
  step*

/-- A successful `extend_from_slice` on bytes appends the slice. -/
theorem extend_from_slice_U8_ok_val {v r : alloc.vec.Vec U8} {sl : Slice U8}
    (h : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v sl = ok r) :
    r.val = v.val ++ sl.val := by
  by_cases hb : v.length + sl.length ≤ Usize.max
  · obtain ⟨w, hw, hp⟩ := WP.spec_imp_exists (extend_from_slice_U8_spec v sl hb)
    rw [h, ok.injEq] at hw
    rw [hw, hp]
  · simp only [alloc.vec.Vec.extend_from_slice, alloc.vec.Vec.length, Slice.length, hb,
      ↓reduceDIte, fail_not_ok] at h

end Aeneas.Std.alloc.vec.Vec
