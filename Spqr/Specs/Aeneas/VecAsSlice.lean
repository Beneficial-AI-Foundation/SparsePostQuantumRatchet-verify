/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import SrcTranslated.Funs

/-! # `alloc::vec::Vec::as_slice`

A successful `as_slice` returns the elements of the vector. -/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.alloc.vec.Vec

/-- A successful `as_slice` returns the elements of the vector. -/
theorem as_slice_ok_val {α : Type} {v : alloc.vec.Vec α} {s : Slice α}
    (h : alloc.vec.Vec.as_slice alloc.alloc.Global v = ok s) : s.val = v.val := by
  simp only [alloc.vec.Vec.as_slice, ok.injEq] at h; subst h; exact Slice.from_val _ _

end Aeneas.Std.alloc.vec.Vec
