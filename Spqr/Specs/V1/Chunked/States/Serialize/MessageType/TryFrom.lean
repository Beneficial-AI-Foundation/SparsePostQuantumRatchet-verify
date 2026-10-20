/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
module

public import SrcTranslated.Funs
import Spqr.Specs.Aeneas.FmtArgumentsFromStr

/-! # Spec theorem for
`spqr::v1::chunked::states::serialize::{impl core::convert::TryFrom<`
`u8, alloc::string::String> for spqr::v1::chunked::states::serialize::MessageType}::try_from`

`try_from` converts a `u8` tag byte back into a `MessageType` variant: `0 ↦ None`, `1 ↦ Hdr`,
`2 ↦ Ek`, `3 ↦ EkCt1Ack`, `4 ↦ Ct1Ack`, `5 ↦ Ct1`, `6 ↦ Ct2`, and returns
`Err(format!("Expected a number between 0 and 6, got {value}"))` for any
other byte. It is the inverse of the derived
`From<MessageType> for u8` conversion and is used by `Message::deserialize` to decode the
message-type tag byte.

The out-of-range branch builds the error string with `format!`, i.e. the external
`alloc::fmt::format`, modelled as an `opaque` function in `SrcTranslated/FunsExternal.lean`.
Its output is unspecified, so the spec below only says the result is *some* `Err`; that the
call succeeds comes from the trusted spec axiom `alloc.fmt.format_spec`
(see `Spqr/Specs/Lib/Version/TryFrom.lean`).

**Source**: src/v1/chunked/states/serialize.rs (lines 107:4-118:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states.serialize.MessageType.Insts.CoreConvertTryFromU8String

/-- **Spec theorem for
`v1.chunked.states.serialize.MessageType.Insts.CoreConvertTryFromU8String.try_from`**:

• The call always succeeds (no panic / no error) for any input byte.
• For an in-range tag byte (`value ≤ 6`) the result is `Ok` of the variant whose discriminant
  is `value`: `0 ↦ None`, `1 ↦ Hdr`, `2 ↦ Ek`, `3 ↦ EkCt1Ack`, `4 ↦ Ct1Ack`, `5 ↦ Ct1`,
  `6 ↦ Ct2`, i.e. `try_from` is a left inverse of `From<MessageType> for u8` on that range.
• For an out-of-range byte (`value > 6`) the result is an `Err` (its message, produced by
  the opaque `alloc.fmt.format`, is left unspecified). -/
@[step]
theorem try_from_spec (value : Std.U8) :
    try_from value ⦃ (result : core.result.Result v1.chunked.states.serialize.MessageType
        String) =>
      match value.val with
        | 0 => result = .Ok .None
        | 1 => result = .Ok .Hdr
        | 2 => result = .Ok .Ek
        | 3 => result = .Ok .EkCt1Ack
        | 4 => result = .Ok .Ct1Ack
        | 5 => result = .Ok .Ct1
        | 6 => result = .Ok .Ct2
        | _ => ∃ e, result = .Err e ⦄ := by
  unfold try_from
  split
  case h_8 h0 h1 h2 h3 h4 h5 h6 =>
    have hv : 6 < value.val := by
      by_contra hle
      have hcases : value.val = 0 ∨ value.val = 1 ∨ value.val = 2 ∨ value.val = 3 ∨
          value.val = 4 ∨ value.val = 5 ∨ value.val = 6 := by omega
      rcases hcases with h | h | h | h | h | h | h
      exacts [h0 (UScalar.eq_of_val_eq h), h1 (UScalar.eq_of_val_eq h),
        h2 (UScalar.eq_of_val_eq h), h3 (UScalar.eq_of_val_eq h), h4 (UScalar.eq_of_val_eq h),
        h5 (UScalar.eq_of_val_eq h), h6 (UScalar.eq_of_val_eq h)]
    simp only [core.hint.must_use, bind_ok]
    step*
    split <;> first | omega | exact ⟨_, rfl⟩
  all_goals (simp only [WP.spec_ok]; exact trivial)

end spqr.v1.chunked.states.serialize.MessageType.Insts.CoreConvertTryFromU8String
