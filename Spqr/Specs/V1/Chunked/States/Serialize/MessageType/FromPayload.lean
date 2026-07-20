/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs

/-! # Spec theorem for
`spqr::v1::chunked::states::serialize::{spqr::v1::chunked::states::serialize::MessageType}`
`::from_payload`

`from_payload` classifies a `MessagePayload` by returning the `MessageType` tag corresponding
to its variant. It ignores the payload contents entirely and maps each `MessagePayload` variant
to the like-named `MessageType` variant.

**Source**: src/v1/chunked/states/serialize.rs (lines 124:4-134:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states.serialize.MessageType

/-- **Spec theorem for
`v1.chunked.states.serialize.MessageType.from_payload`**:

• The call always succeeds (no panic / no error) for any input `mp`.
• The resulting `MessageType` is the tag of `mp`: each `MessagePayload` variant maps to the
  identically-named `MessageType` variant, discarding any payload data. -/
@[step]
theorem from_payload_spec (mp : v1.chunked.states.MessagePayload) :
    from_payload mp ⦃ (result : v1.chunked.states.serialize.MessageType) =>
      result = match mp with
        | .None => .None
        | .Hdr _ => .Hdr
        | .Ek _ => .Ek
        | .EkCt1Ack _ => .EkCt1Ack
        | .Ct1Ack _ => .Ct1Ack
        | .Ct1 _ => .Ct1
        | .Ct2 _ => .Ct2 ⦄ := by
  match mp with
  | .None | .Hdr _ | .Ek _ | .EkCt1Ack _ | .Ct1Ack _ | .Ct1 _ | .Ct2 _ =>
    simp only [from_payload, WP.spec_ok]

end spqr.v1.chunked.states.serialize.MessageType
