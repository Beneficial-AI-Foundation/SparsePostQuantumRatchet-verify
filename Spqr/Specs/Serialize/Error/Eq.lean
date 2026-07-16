/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs

/-! # Spec theorem for
`spqr::serialize::{impl core::cmp::PartialEq<spqr::serialize::Error>`
`for spqr::serialize::Error}::eq`

The derived `PartialEq` for the fieldless enum `serialize::Error` compares the two values by
reading their discriminants.

**Source**: src/serialize.rs (line 6, `#[derive(..., PartialEq)]`)
-/

open Aeneas Aeneas.Std Result

namespace spqr.serialize.Error

/-
natural language description:

• Takes two `serialize::Error` values `self` and `other`. The enum has exactly two fieldless
  variants: `Deserialization` and `EncodingDecoding`.
• Reads the discriminant of each value (0 for `Deserialization`, 1 for `EncodingDecoding`)
  and compares the discriminants.
• Returns `ok true` if the discriminants are equal, `ok false` otherwise.

natural language specs:

• The function always succeeds (no panic / no error) for any pair of inputs.
• Since every variant is fieldless, discriminant equality coincides with equality of the
  values themselves: `eq(a, b) = ok (a = b)`.
• The relation is reflexive, symmetric, and transitive.
-/

/-- **Spec theorem for `serialize.Error.Insts.CoreCmpPartialEqError.eq`**:

The derived `PartialEq<Error> for Error` always succeeds and returns `true` if and only if
the two values are equal. The implementation compares discriminants, and because both
variants of `serialize::Error` are fieldless, discriminant equality is equivalent to
propositional equality of the values. -/
@[step]
theorem eq_spec (self other : serialize.Error) :
    Insts.CoreCmpPartialEqError.eq self other ⦃ (result : Bool) =>
      result = true ↔ self = other ⦄ := by
  simp only [Insts.CoreCmpPartialEqError.eq]
  match self, other with
  | .Deserialization, .Deserialization
  | .Deserialization, .EncodingDecoding
  | .EncodingDecoding, .Deserialization
  | .EncodingDecoding, .EncodingDecoding => simp [Error.read_discriminant]

end spqr.serialize.Error
