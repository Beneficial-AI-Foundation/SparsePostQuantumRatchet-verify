/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
module

public import Aeneas

/-! # Staged for upstream to Aeneas `Std/Slice.lean` -/

@[expose] public section

open Aeneas Aeneas.Std

/-- The empty slice, e.g. to index a list of slices (such as the chunks of a `ChunksExact`
iterator) with `[k]!`. -/
noncomputable instance Aeneas.Std.Slice.instInhabited {α : Type} : Inhabited (Slice α) :=
  ⟨Slice.from [] (by simp)⟩
