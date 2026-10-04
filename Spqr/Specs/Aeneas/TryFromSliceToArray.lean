/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `<[T; N] as TryFrom<&[T]>>::try_from`

Converts a slice `&[T]` to `[T; N]`, succeeding when `slice.len() == N`. With identity `Copy`,
the array elements equal the slice elements. Used in `.try_into().unwrap()` idioms.

**Source**: core/src/array/mod.rs (TryFrom impl for [T; N])
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.core.array.TryFromArrayCopySlice

/--
**Spec theorem for `core.array.TryFromArrayCopySlice.try_from`**:

If `s.length = N` and `Copy` is the identity, returns `Ok a` with `a.val = s.val`.

**Source**: core/src/array/mod.rs (TryFrom impl for [T; N])
-/
@[step]
theorem try_from_spec {T : Type} (N : Usize) (copyInst : core.marker.Copy T)
    (s : Slice T)
    (h_len : s.length = N) :
    core.array.TryFromArrayCopySlice.try_from N copyInst s ⦃ result =>
      ∃ (a : Array T N), result = .Ok a ∧ a.val = s.val ⦄ := by
  unfold core.array.TryFromArrayCopySlice.try_from
  simp only [dif_pos h_len, WP.spec_ok]
  exact ⟨⟨s.val, by scalar_tac⟩, rfl, rfl⟩

end Aeneas.Std.core.array.TryFromArrayCopySlice
