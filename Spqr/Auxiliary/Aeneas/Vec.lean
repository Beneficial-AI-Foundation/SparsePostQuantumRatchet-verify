/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import Aeneas

/-!
# `Vec` helpers (staged for upstream to Aeneas `Std/Vec.lean`)

`alloc.vec.Vec.deref` returns a `Slice` carrying the same underlying list, hence the same `val` and
`length`. These simp lemmas expose that so `simp`/`scalar_tac` can see through a `.deref`.
-/

open Aeneas Aeneas.Std

-- TODO: upstream to Aeneas (`Std/Vec.lean`); `Vec.deref` carries the same `val`, hence `length`.
@[simp] theorem _root_.Aeneas.Std.alloc.vec.Vec.deref_val {α : Type} (v : alloc.vec.Vec α) :
    (alloc.vec.Vec.deref v).val = v.val := rfl

@[simp, scalar_tac_simps] theorem _root_.Aeneas.Std.alloc.vec.Vec.deref_length {α : Type}
    (v : alloc.vec.Vec α) : (alloc.vec.Vec.deref v).length = v.length := rfl
