/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Lib.MsgVersion.Defs
/-!
# Spec theorem for `spqr::msg_version`

Extracts protocol version from the first byte of a serialized message.
Empty → `V0`, `0` → `V0`, `1` → `V1`, otherwise → `none`.

**Source**: src/lib.rs (lines 464:0-470:1)
-/

open Aeneas Aeneas.Std

namespace spqr

/-- **Spec theorem for `spqr.msg_version`**:

* Empty message → `some V0` (default version).
* First byte `0x00` → `some V0`.
* First byte `0x01` → `some V1`.
* Any other first byte → `none` (unsupported version).

No preconditions needed; never panics. -/
@[step]
theorem msg_version_spec (msg : alloc.vec.Vec U8) :
    msg_version msg ⦃ (result : Option proto.pq_ratchet.Version) =>
      result = msgVersionExpected msg ⦄ := by
  unfold msg_version
  cases h_msg : msg.val with
  | nil =>
    step*
    · simp_all [msgVersionExpected, firstByte]
    · simp [List.isEmpty, h_msg] at b_post; simp_all
  | cons hd rest =>
    step*
    · simp [List.isEmpty, h_msg] at b_post; simp_all
    · have hi : i = hd := by simp_all
      rw [hi]
      unfold proto.pq_ratchet.Version.Insts.CoreConvertTryFromU8String.try_from
      split
      · simp only [core.result.Result.ok, bind_tc_ok, WP.spec_ok,
          msgVersionExpected, firstByte, versionOfByte]
        simp_all [show ((0#8#uscalar : U8)).val = 0 from rfl]
      · simp only [core.result.Result.ok, bind_tc_ok, WP.spec_ok,
          msgVersionExpected, firstByte, versionOfByte]
        simp_all [show ((1#8#uscalar : U8)).val = 1 from rfl]
      · step*
        simp only [core.result.Result.ok, WP.spec_ok, msgVersionExpected, firstByte, versionOfByte]
        simp_all
        split <;>
          simp_all [show ((0#8#uscalar : U8)).val = 0 from rfl,
            show ((1#8#uscalar : U8)).val = 1 from rfl]

end spqr
