/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import SrcTranslated.Funs

/-! # `alloc::vec::Vec::append`

A successful `append` returns the elements of the first vector followed by those of the
second. -/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.alloc.vec.Vec

/-- A successful `append` returns the elements of `v1` followed by those of `v2`. -/
theorem append_ok_val {α : Type} {v1 v2 r1 r2 : alloc.vec.Vec α}
    (h : alloc.vec.Vec.append alloc.alloc.Global v1 v2 = ok (r1, r2)) : r1.val = v1.val ++ v2.val := by
  simp only [alloc.vec.Vec.append] at h
  split at h
  · simp only [ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]; simp
  · exact absurd h fail_not_ok

end Aeneas.Std.alloc.vec.Vec
