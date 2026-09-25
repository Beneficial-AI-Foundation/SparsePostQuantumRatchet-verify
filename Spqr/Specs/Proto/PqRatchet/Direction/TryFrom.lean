/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-! # Spec theorem for
`spqr::proto::pq_ratchet::{impl core::convert::TryFrom<i32, prost::error::UnknownEnumValue>`
`for spqr::proto::pq_ratchet::Direction}::try_from`

Converts `i32` to `Direction`: `0 ↦ A2B`, `1 ↦ B2A`, else `Err(value)`.
Inverse of `From<Direction> for i32` on valid discriminants; used by protobuf deserialization.

**Source**: generated/signal.proto.pq_ratchet.rs -/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue

/-- **Spec theorem for
`proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from`**:

Always succeeds: `0 ↦ Ok A2B`, `1 ↦ Ok B2A`, otherwise `Err value`. -/
@[step]
theorem try_from_spec (value : Std.I32) :
    try_from value ⦃ (result : core.result.Result proto.pq_ratchet.Direction
        prost.error.UnknownEnumValue) =>
      result = match value with
        | 0#iscalar => .Ok .A2B
        | 1#iscalar => .Ok .B2A
        | _ => .Err value ⦄ := by
  unfold try_from
  generalize hp : ((match value with
    | 0#iscalar => .Ok .A2B
    | 1#iscalar => .Ok .B2A
    | _ => .Err value :
    core.result.Result proto.pq_ratchet.Direction prost.error.UnknownEnumValue)) = expected
  split <;> (simp only [WP.spec_ok]; subst hp; grind)

end spqr.proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue
