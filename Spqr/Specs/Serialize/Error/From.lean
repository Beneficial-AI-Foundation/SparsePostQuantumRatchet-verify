/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs

/-! # Spec theorem for
`spqr::serialize::{impl core::convert::From<spqr::encoding::polynomial::PolynomialError>`
`for spqr::serialize::Error}::from`

This is the `From` conversion that maps any `polynomial::PolynomialError` to the
`serialize::Error::EncodingDecoding` variant, letting the `?` operator turn a
polynomial-layer error into a serialization-layer error automatically. The input
error is discarded: every polynomial error collapses to `EncodingDecoding`.

**Source**: src/serialize.rs (lines 14:0-18:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr.serialize.Error.Insts.CoreConvertFromPolynomialError

/-- **Spec theorem for
`impl From<PolynomialError> for serialize::Error::from`**:

• The call always succeeds (no panic).
• The result is the constant `serialize.Error.EncodingDecoding`, regardless of the
  input error:
    `from _e = ok serialize.Error.EncodingDecoding`. -/
@[step]
theorem from_spec (_e : encoding.polynomial.PolynomialError) :
    «from» _e ⦃ (result : serialize.Error) =>
      result = serialize.Error.EncodingDecoding ⦄ := by
  simp [«from»]

end spqr.serialize.Error.Insts.CoreConvertFromPolynomialError
