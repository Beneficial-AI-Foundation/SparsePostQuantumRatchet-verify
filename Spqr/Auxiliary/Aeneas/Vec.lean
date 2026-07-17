/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import Aeneas

/-! # Staged for upstream to Aeneas `Std/Vec.lean` -/

open Aeneas Aeneas.Std

@[simp, grind =] theorem _root_.Aeneas.Std.alloc.vec.Vec.deref_val {α : Type}
    (v : alloc.vec.Vec α) : (alloc.vec.Vec.deref v).val = v.val := rfl

@[simp, scalar_tac_simps, grind =] theorem _root_.Aeneas.Std.alloc.vec.Vec.deref_length {α : Type}
    (v : alloc.vec.Vec α) : (alloc.vec.Vec.deref v).length = v.length := rfl
