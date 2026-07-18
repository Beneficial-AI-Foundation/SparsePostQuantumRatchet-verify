/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-! # Spec theorem for `spqr::encoding::polynomial::{PolyEncoder}::get_encoder_state`

Pure accessor returning the `EncoderState` from a `PolyEncoder`'s `s` field:
  `get_encoder_state self = ok self.s`

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial.PolyEncoder

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.get_encoder_state`**:

Infallible projection: `get_encoder_state self = ok self.s`. -/
@[step]
theorem get_encoder_state_spec (self : encoding.polynomial.PolyEncoder) :
    get_encoder_state self ⦃ (result : encoding.polynomial.EncoderState) =>
      result = self.s ⦄ := by
  simp [get_encoder_state]

end spqr.encoding.polynomial.PolyEncoder
