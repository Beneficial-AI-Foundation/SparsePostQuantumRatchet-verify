/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-! # Spec theorem for
`spqr::proto::pq_ratchet::{impl core::convert::TryFrom<i32, prost::error::UnknownEnumValue>`
`for spqr::proto::pq_ratchet::Version}::try_from`

`try_from` converts an `i32` value into a `Version` variant: `0 ↦ V0`, `1 ↦ V1`, and returns
`Err(value)` (an `UnknownEnumValue` wrapping the unrecognised `i32`) for any other value.
It is the inverse of the derived `From<Version> for i32` conversion on the valid range and is
used by the protobuf deserialization layer to decode the `Version` enum field.

**Source**: generated/signal.proto.pq_ratchet.rs -/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.Version.Insts.CoreConvertTryFromI32UnknownEnumValue

/-- **Spec theorem for
`proto.pq_ratchet.Version.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from`**:

• The call always succeeds (no panic / no error) for any `I32` input.
• For a recognised discriminant (`value = 0` or `value = 1`) the result is `Ok` of the
  corresponding `Version` variant: `0 ↦ V0`, `1 ↦ V1`, i.e. `try_from` is a left inverse
  of `From<Version> for i32` on that range.
• For any other `i32` value the result is `Err value` (an `UnknownEnumValue`). -/
@[step]
theorem try_from_spec (value : Std.I32) :
    try_from value ⦃ (result : core.result.Result proto.pq_ratchet.Version
        prost.error.UnknownEnumValue) =>
      result = match value with
        | 0#iscalar => .Ok .V0
        | 1#iscalar => .Ok .V1
        | _ => .Err value ⦄ := by
  unfold try_from
  generalize hp : ((match value with
    | 0#iscalar => .Ok .V0
    | 1#iscalar => .Ok .V1
    | _ => .Err value :
    core.result.Result proto.pq_ratchet.Version prost.error.UnknownEnumValue)) = expected
  split <;> (simp only [WP.spec_ok]; subst hp; grind)

end spqr.proto.pq_ratchet.Version.Insts.CoreConvertTryFromI32UnknownEnumValue
