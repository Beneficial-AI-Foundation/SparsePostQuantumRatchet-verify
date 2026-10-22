/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs

/-! # Spec theorem for `decoded_message` closure `call_mut`

The closure `|_| None` in `decoded_message` ignores its index argument and
returns `none : Option Poly`. It captures nothing, so the closure state is
unchanged. The extracted `call_mut` returns `none` paired with the unchanged
closure state.

**Source**: spqr/src/encoding/polynomial.rs, lines 942:65-942:73 -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial

namespace spqr.encoding.polynomial.DecoderPolyDecoder.decoded_message.closure
namespace Insts.CoreOpsFunctionFnMutTupleUsizeOptionPoly

/-- **Spec theorem for `DecoderPolyDecoder.decoded_message.closure.call_mut`**:

Always succeeds. Returns `none` with the closure state unchanged:
`result.1 = none` and `result.2 = c`. -/
@[step]
theorem call_mut_spec
    (c : DecoderPolyDecoder.decoded_message.closure)
    (tupled_args : Usize) :
    call_mut c tupled_args ⦃ (result : (Option Poly) ×
    DecoderPolyDecoder.decoded_message.closure) =>
      result.1 = none ∧
      result.2 = c ⦄ := by
  unfold call_mut
  simp

end Insts.CoreOpsFunctionFnMutTupleUsizeOptionPoly
end spqr.encoding.polynomial.DecoderPolyDecoder.decoded_message.closure
