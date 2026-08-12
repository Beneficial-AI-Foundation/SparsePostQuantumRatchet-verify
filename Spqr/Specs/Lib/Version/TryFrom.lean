/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-! # Spec theorem for `spqr::{impl TryFrom<u8, String> for Version}::try_from`

Converts `u8` to `Version`: `0 → V0`, `1 → V1`, else `Err("Expected 0 or 1")`.

**Source**: spqr/src/lib.rs -/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.Version.Insts.CoreConvertTryFromU8String

/-- **Spec theorem for `spqr.proto.pq_ratchet.Version.Insts.CoreConvertTryFromU8String.try_from`**:

Maps `0 ↔ Ok V0`, `1 ↔ Ok V1`, `otherwise ↔ Err "Expected 0 or 1"`. No panic; errors via
`core.result.Result.Err`. -/
@[step]
theorem try_from_spec (value : U8) :
    try_from value ⦃ (result : core.result.Result proto.pq_ratchet.Version String) =>
      (value = 0#u8 ↔ result = core.result.Result.Ok proto.pq_ratchet.Version.V0) ∧
      (value = 1#u8 ↔ result = core.result.Result.Ok proto.pq_ratchet.Version.V1) ∧
      ((value ≠ 0#u8 ∧ value ≠ 1#u8) ↔ result = core.result.Result.Err "Expected 0 or 1") ⦄ := by
  suffices h : try_from value ⦃ (result : core.result.Result proto.pq_ratchet.Version String) =>
      result = match value.val with
        | 0 => .Ok proto.pq_ratchet.Version.V0
        | 1 => .Ok proto.pq_ratchet.Version.V1
        | _ => .Err "Expected 0 or 1" ⦄ by
    apply WP.spec_mono h
    intro result hr
    subst hr
    refine ⟨⟨fun hv => by simp [hv], fun hr => ?_⟩,
            ⟨fun hv => by simp [hv], fun hr => ?_⟩,
            ⟨fun ⟨hne0, hne1⟩ => ?_, fun hr => ?_⟩⟩
    · by_contra hne
      have hv0 : value.val ≠ 0 := fun h => hne (by ext; grind)
      split at hr <;> simp_all
    · by_contra hne
      have hv1 : value.val ≠ 1 := fun h => hne (by ext; grind)
      split at hr <;> simp_all
    · have hv0 : value.val ≠ 0 := fun h => hne0 (by ext; grind)
      have hv1 : value.val ≠ 1 := fun h => hne1 (by ext; grind)
      split <;> simp_all
    · split at hr <;> simp_all
  unfold try_from
  generalize hp : ((match value.val with
    | 0 => .Ok proto.pq_ratchet.Version.V0
    | 1 => .Ok proto.pq_ratchet.Version.V1
    | _ => .Err "Expected 0 or 1" :
    core.result.Result proto.pq_ratchet.Version String)) = expected
  split <;>
    first
    | (simp only [WP.spec_ok]; subst hp; rfl)
    | step*
      grind

end spqr.proto.pq_ratchet.Version.Insts.CoreConvertTryFromU8String
