/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::chain_from_version_negotiation::{impl FnOnce for closure}::call_once`

The closure `|_| Error::StateDecode` comes from
`vn.direction.try_into().map_err(|_| Error::StateDecode)?` in
`chain_from_version_negotiation`. It maps a failed `Direction` conversion
(`prost::error::UnknownEnumValue`) to `Error::StateDecode`. It captures nothing,
so its state type is extracted as `Unit` and its body is constant.

**Source**: spqr/src/lib.rs -/

open Aeneas Aeneas.Std Result

namespace spqr.chain_from_version_negotiation.closure.Insts
namespace CoreOpsFunctionFnOnceTupleUnknownEnumValueError

/-- **Spec theorem for `chain_from_version_negotiation.closure.call_once`**:

• Takes the empty closure state `c` (extracted as `Unit`) and the argument
  `tupled_args : prost.error.UnknownEnumValue`.
• Ignores both inputs and returns `ok Error.StateDecode`; it never panics.
• Via `map_err`, an unknown `direction` value in `chain_from_version_negotiation`
  is always mapped to `Error.StateDecode`. -/
@[step]
theorem call_once_spec
    (c : chain_from_version_negotiation.closure)
    (tupled_args : prost.error.UnknownEnumValue) :
    call_once c tupled_args ⦃ (result : Error) =>
      result = Error.StateDecode ⦄ := by
  unfold call_once
  step*

end CoreOpsFunctionFnOnceTupleUnknownEnumValueError
end spqr.chain_from_version_negotiation.closure.Insts
