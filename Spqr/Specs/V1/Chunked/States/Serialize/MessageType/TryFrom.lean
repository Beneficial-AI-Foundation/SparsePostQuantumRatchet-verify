/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs

/-! # Spec theorem for
`spqr::v1::chunked::states::serialize::{impl core::convert::TryFrom<`
`u8, alloc::string::String> for spqr::v1::chunked::states::serialize::MessageType}::try_from`

`try_from` converts a `u8` tag byte back into a `MessageType` variant: `0 ↦ None`, `1 ↦ Hdr`,
`2 ↦ Ek`, `3 ↦ EkCt1Ack`, `4 ↦ Ct1Ack`, `5 ↦ Ct1`, `6 ↦ Ct2`, and returns
`Err("Expected a number between 0 and 6")` for any other byte. It is the inverse of the derived
`From<MessageType> for u8` conversion and is used by `Message::deserialize` to decode the
message-type tag byte.

The out-of-range branch builds the error string via the external function
`Str.Insts.AllocBorrowToOwnedString.to_owned`, modeled in `SrcTranslated/FunsExternal.lean` as
UTF-8 decoding of the slice's bytes; the spec theorem `to_owned_eq` proved there shows the call
succeeds and returns the same string, which lets the spec below cover the full input range.

**Source**: src/v1/chunked/states/serialize.rs (lines 109:4-120:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states.serialize.MessageType.Insts.CoreConvertTryFromU8String

/-- **Spec theorem for
`v1.chunked.states.serialize.MessageType.Insts.CoreConvertTryFromU8String.try_from`**:

• The call always succeeds (no panic / no error) for any input byte.
• For an in-range tag byte (`value ≤ 6`) the result is `Ok` of the variant whose discriminant
  is `value`: `0 ↦ None`, `1 ↦ Hdr`, `2 ↦ Ek`, `3 ↦ EkCt1Ack`, `4 ↦ Ct1Ack`, `5 ↦ Ct1`,
  `6 ↦ Ct2`, i.e. `try_from` is a left inverse of `From<MessageType> for u8` on that range.
• For an out-of-range byte (`value > 6`) the result is
  `Err "Expected a number between 0 and 6"`. -/
@[step]
theorem try_from_spec (value : Std.U8) :
    try_from value ⦃ (result : core.result.Result v1.chunked.states.serialize.MessageType
        String) =>
      result = match value.val with
        | 0 => .Ok .None
        | 1 => .Ok .Hdr
        | 2 => .Ok .Ek
        | 3 => .Ok .EkCt1Ack
        | 4 => .Ok .Ct1Ack
        | 5 => .Ok .Ct1
        | 6 => .Ok .Ct2
        | _ => .Err "Expected a number between 0 and 6" ⦄ := by
  unfold try_from
  generalize hp : ((match value.val with
    | 0 => .Ok .None
    | 1 => .Ok .Hdr
    | 2 => .Ok .Ek
    | 3 => .Ok .EkCt1Ack
    | 4 => .Ok .Ct1Ack
    | 5 => .Ok .Ct1
    | 6 => .Ok .Ct2
    | _ => .Err "Expected a number between 0 and 6" :
    core.result.Result v1.chunked.states.serialize.MessageType String)) = expected
  split <;>
    first
    | (simp only [WP.spec_ok]; subst hp; rfl)
    | step*
      grind

end spqr.v1.chunked.states.serialize.MessageType.Insts.CoreConvertTryFromU8String
