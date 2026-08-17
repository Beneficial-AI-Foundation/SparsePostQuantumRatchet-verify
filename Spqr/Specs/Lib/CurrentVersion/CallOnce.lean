/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `current_version::closure::call_once`

The closure `|_| Error::StateDecode` from `map_err` in `current_version` (src/lib.rs, line 259).
It ignores the `UnknownEnumValue` argument and always returns `Error::StateDecode`.
Aeneas extracts the closure state as `Unit` (no captures).

**Source**: spqr/src/lib.rs -/

open Aeneas Aeneas.Std Result

namespace spqr.current_version.closure.Insts.CoreOpsFunctionFnOnceTupleUnknownEnumValueError

/--
**Spec theorem for `current_version.closure.call_once`**:

Ignores both the closure state and `UnknownEnumValue` argument, always returning
`ok Error.StateDecode`. -/
@[step]
theorem call_once_spec
    (c : current_version.closure)
    (tupled_args : prost.error.UnknownEnumValue) :
    call_once c tupled_args  ⦃ (result : Error) =>
      result = Error.StateDecode ⦄ := by
  unfold call_once
  step*

end spqr.current_version.closure.Insts.CoreOpsFunctionFnOnceTupleUnknownEnumValueError
