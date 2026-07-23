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

The spec below is restricted to in-range inputs (`value ≤ 6`): in the out-of-range branch the
extracted code builds the error string via the external function
`Str.Insts.AllocBorrowToOwnedString.to_owned`, which is an opaque axiom in
`SrcTranslated/FunsExternal.lean`, so no unconditional success spec can be proven for it.

**Source**: src/v1/chunked/states/serialize.rs (lines 109:4-120:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states.serialize.MessageType.Insts.CoreConvertTryFromU8String

/-- **Spec theorem for
`v1.chunked.states.serialize.MessageType.Insts.CoreConvertTryFromU8String.try_from`**:

• For any in-range tag byte (`value ≤ 6`) the call succeeds (no panic / no error).
• The result is `Ok` of the variant whose discriminant is `value`:
  `0 ↦ None`, `1 ↦ Hdr`, `2 ↦ Ek`, `3 ↦ EkCt1Ack`, `4 ↦ Ct1Ack`, `5 ↦ Ct1`, `6 ↦ Ct2`,
  i.e. `try_from` is a left inverse of `From<MessageType> for u8` on the valid tag range. -/
@[step]
theorem try_from_spec (value : Std.U8) (h : value.val ≤ 6) :
    try_from value ⦃ (result : core.result.Result v1.chunked.states.serialize.MessageType
        String) =>
      result = .Ok (match value.val with
        | 0 => .None
        | 1 => .Hdr
        | 2 => .Ek
        | 3 => .EkCt1Ack
        | 4 => .Ct1Ack
        | 5 => .Ct1
        | _ => .Ct2) ⦄ := by
  unfold try_from
  split <;>
    first
    | (simp only [WP.spec_ok]; rfl)
    | (exfalso
       rcases value with ⟨bv⟩
       simp_all only [UScalar.val, UScalar.mk.injEq, BitVec.toNat_eq, UScalarTy.U8_numBits_eq,
         Nat.reducePow, BitVec.toNat_ofNat, Nat.reduceMod, imp_false]
       omega)

end spqr.v1.chunked.states.serialize.MessageType.Insts.CoreConvertTryFromU8String
