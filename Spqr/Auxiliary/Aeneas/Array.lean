/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import Aeneas

/-!
# `Array` helpers (staged for upstream to Aeneas `Std/Array/Array.lean`)

`Array.make` currently has no `val`/`length` simp lemmas; this exposes its underlying list so `simp`
can see through it (mirrors `Array.val_to_slice` in `Std/Array/ArraySlice.lean`).
-/

open Aeneas Aeneas.Std

-- TODO: upstream to Aeneas (`Std/Array/Array.lean`).
@[simp, grind =] theorem _root_.Aeneas.Std.Array.val_make {α : Type}
    (n : Usize) (l : List α) (h) : (Array.make n l h).val = l := rfl
