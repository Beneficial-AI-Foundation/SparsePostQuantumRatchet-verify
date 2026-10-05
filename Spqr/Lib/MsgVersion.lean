/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::msg_version`

Extracts protocol version from the first byte of a serialized message.
Empty → `V0`, `0` → `V0`, `1` → `V1`, otherwise → `none`.

**Source**: src/lib.rs (lines 464:0-470:1)
-/

open Aeneas Aeneas.Std

namespace spqr

/-- **Spec theorem for `spqr.msg_version`**:
Non-empty message: maps first byte `0` → `V0`, `1` → `V1`, else → `none`.
Never panics since index `0` is always valid. -/
@[step]
theorem msg_version_spec (msg : alloc.vec.Vec U8) (h_nonempty : ¬msg.val = []) :
    msg_version msg ⦃ (result : Option proto.pq_ratchet.Version) =>
      result = match (↑msg : List U8)[0]!.val with
        | 0 => some proto.pq_ratchet.Version.V0
        | 1 => some proto.pq_ratchet.Version.V1
        | _ => none ⦄ := by
  unfold msg_version
  step*
  case hbound => simp_all [List.length_pos_iff]
  · simp_all
  · have hi : (↑msg : List U8)[0]! = i := by
      rw [getElem!_pos (↑msg : List U8) 0 (by simp_all [List.length_pos_iff]), i_post]
    rw [hi]
    unfold proto.pq_ratchet.Version.Insts.CoreConvertTryFromU8String.try_from
    split
    · simp only [core.result.Result.ok, bind_tc_ok, WP.spec_ok]; rfl
    · simp only [core.result.Result.ok, bind_tc_ok, WP.spec_ok]; rfl
    · step*
      simp only [core.result.Result.ok, WP.spec_ok]
      split <;>
        simp_all [show ((0#8#uscalar : U8)).val = 0 from rfl,
          show ((1#8#uscalar : U8)).val = 1 from rfl]

@[step]
theorem msg_version_spec_empty (msg : alloc.vec.Vec U8) (h_empty : msg.val = []) :
    msg_version msg ⦃ (result : Option proto.pq_ratchet.Version) =>
      result = some proto.pq_ratchet.Version.V0 ⦄ := by
  unfold msg_version
  step*
  simp_all

end spqr
