/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-! # Spec theorem for `decode_state::closure::call_once`

The closure `|_| Error::StateDecode` from `map_err` in `decode_state` (src/lib.rs, line 480).
It ignores the `DecodeError` argument and always returns `Error::StateDecode`.
Aeneas extracts the closure state as `Unit` (no captures).

**Source**: spqr/src/lib.rs -/

open Aeneas Aeneas.Std Result

namespace spqr.decode_state.closure.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorError

/-- **Spec theorem for `decode_state.closure.call_once`**:

Ignores both the closure state and `DecodeError` argument, always returning `ok Error.StateDecode`.
-/
@[step]
theorem call_once_spec
    (c : decode_state.closure)
    (tupled_args : prost.error.DecodeError) :
    call_once c tupled_args  ⦃ (result : Error) =>
      result = Error.StateDecode ⦄ := by
  unfold call_once
  step*

end spqr.decode_state.closure.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorError
