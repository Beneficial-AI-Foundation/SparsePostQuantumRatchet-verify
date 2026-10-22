/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

import Spqr.Specs.Encoding.Polynomial.PolyDecoder.DecodedMessage.CallMut
public import SrcTranslated.Funs

/-! # Spec theorem for `decoded_message` closure `call_once`

The closure `|_| None` in `decoded_message` ignores its index argument and
returns `none : Option Poly`. It captures nothing, so the closure state is
`Unit`. The extracted `call_once` delegates to `call_mut` and returns
just the resulting `Option Poly` (without the closure state).

**Source**: spqr/src/encoding/polynomial.rs, lines 942:65-942:73 -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial

namespace spqr.encoding.polynomial.DecoderPolyDecoder.decoded_message.closure
namespace Insts.CoreOpsFunctionFnOnceTupleUsizeOptionPoly

/-- **Spec theorem for `DecoderPolyDecoder.decoded_message.closure.call_once`**:

Always succeeds. Returns `none`:
`result = none`. -/
@[step]
theorem call_once_spec
    (c : DecoderPolyDecoder.decoded_message.closure)
    (i : Usize) :
    call_once c i ⦃ (result : Option Poly) =>
      result = none ⦄ := by
  unfold call_once
  step*

end Insts.CoreOpsFunctionFnOnceTupleUsizeOptionPoly
end spqr.encoding.polynomial.DecoderPolyDecoder.decoded_message.closure
