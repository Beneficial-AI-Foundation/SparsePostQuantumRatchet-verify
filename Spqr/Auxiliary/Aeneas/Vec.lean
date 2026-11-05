/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
module

public import Aeneas


/-! # Staged for upstream to Aeneas `Std/Vec.lean` -/

@[expose] public section
-- https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/305

open Aeneas Aeneas.Std

@[simp, grind =] theorem _root_.Aeneas.Std.alloc.vec.Vec.deref_val {α : Type}
    (v : alloc.vec.Vec α) : (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref]

@[scalar_tac_simps, grind =] theorem _root_.Aeneas.Std.alloc.vec.Vec.deref_length {α : Type}
    (v : alloc.vec.Vec α) : (alloc.vec.Vec.deref v).length = v.length := by
  simp [alloc.vec.Vec.deref]

namespace Aeneas.Std.alloc.vec.Vec

open Result

/-- A successful `push` adds one element. -/
theorem push_ok_length {α : Type} {v v' : alloc.vec.Vec α} {x : α}
    (h : alloc.vec.Vec.push v x = ok v') : v'.val.length = v.val.length + 1 := by
  unfold alloc.vec.Vec.push at h
  dsimp only at h
  split at h
  · simp only [ok.injEq] at h; subst h; simp
  · exact absurd h fail_not_ok

end Aeneas.Std.alloc.vec.Vec
