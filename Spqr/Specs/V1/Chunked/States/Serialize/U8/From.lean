/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs

/-! # Spec theorem for
`spqr::v1::chunked::states::serialize::{impl core::convert::From<`
`spqr::v1::chunked::states::serialize::MessageType> for u8}::from`

This is the `From` conversion (derived by `#[derive(IntoPrimitive)]`) from the `#[repr(u8)]`
fieldless enum `MessageType` to `u8`. It reads the discriminant of the input variant and returns
it as a `u8`: `None ↦ 0`, `Hdr ↦ 1`, `Ek ↦ 2`, `EkCt1Ack ↦ 3`, `Ct1Ack ↦ 4`, `Ct1 ↦ 5`,
`Ct2 ↦ 6`. `Message::serialize` uses it to emit the message-type tag byte.

**Source**: src/v1/chunked/states/serialize.rs (lines 95:9-95:22)
-/

open Aeneas Aeneas.Std Result

namespace spqr.U8.Insts.CoreConvertFromMessageType

/-- **Spec theorem for `U8.Insts.CoreConvertFromMessageType.from`**:

• The call always succeeds (no panic).
• The result is the discriminant of the input variant:
  `None ↦ 0`, `Hdr ↦ 1`, `Ek ↦ 2`, `EkCt1Ack ↦ 3`, `Ct1Ack ↦ 4`, `Ct1 ↦ 5`, `Ct2 ↦ 6`. -/
@[step]
theorem from_spec (enum_value : v1.chunked.states.serialize.MessageType) :
    «from» enum_value ⦃ (result : Std.U8) =>
      result.val = match enum_value with
        | .None => 0
        | .Hdr => 1
        | .Ek => 2
        | .EkCt1Ack => 3
        | .Ct1Ack => 4
        | .Ct1 => 5
        | .Ct2 => 6 ⦄ := by
  match enum_value with
  | .None | .Hdr | .Ek | .EkCt1Ack | .Ct1Ack | .Ct1 | .Ct2 =>
    simp only [«from», read_discriminant, v1.chunked.states.serialize.MessageType.read_discriminant,
      WP.spec_ok, UScalarTy.U8_numBits_eq, Std.le_refl,
      UScalar.cast_val_mod_pow_greater_numBits_eq, UScalar.ofNatCore_val_eq]

end spqr.U8.Insts.CoreConvertFromMessageType
