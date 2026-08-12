/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for
# `spqr::{impl core::convert::From<spqr::encoding::EncodingError> for spqr::Error}::from`

Lifts an encoding error into `spqr::Error` via the `Error::EncodingDecoding` constructor.
A pure, infallible, injective constructor application.

**Source**: spqr/src/lib.rs -/

open Aeneas Aeneas.Std Result

namespace spqr.Error.Insts.CoreConvertFromEncodingError

/-- **Spec theorem for `spqr.Error.Insts.CoreConvertFromEncodingError.from`**:

• Wraps `e : encoding.EncodingError` in `Error.EncodingDecoding`.
• Always succeeds: returns `ok (Error.EncodingDecoding e)`.

Postcondition: `result = Error.EncodingDecoding e`. -/
@[step]
theorem from_spec (e : encoding.EncodingError) :
    «from» e ⦃ (result : Error) =>
      result = Error.EncodingDecoding e ⦄ := by
  unfold «from»
  simp

end spqr.Error.Insts.CoreConvertFromEncodingError

/-! # Spec theorem for `spqr::{impl From<authenticator::Error> for Error}::from`

Maps every `authenticator::Error` to `Error::MacVerifyFailed`. The mapping is
**lossy**: the specific authenticator error is discarded so MAC verification
failures do not leak their failure mode.

**Source**: spqr/src/lib.rs -/

open Aeneas Aeneas.Std Result

namespace spqr.Error.Insts.CoreConvertFromError

/-- **Spec theorem for `spqr.Error.Insts.CoreConvertFromError.from`**:

• Discards the input `v : authenticator.Error`.
• Always succeeds: returns `ok Error.MacVerifyFailed` (constant mapping).

Postcondition: `result = Error.MacVerifyFailed`. -/
@[step]
theorem from_spec (v : authenticator.Error) :
    Error.Insts.CoreConvertFromError.from v ⦃ (result : Error) =>
      result = Error.MacVerifyFailed ⦄ := by
  unfold Error.Insts.CoreConvertFromError.from
  simp_all

end spqr.Error.Insts.CoreConvertFromError
