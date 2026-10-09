/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang, Markus Dablander
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Serialize.Authenticator.IntoPb
import Spqr.Specs.V1.Unchunked.SendEk.Serialize.EkSentCt1Received.FunctionalModels

/-!
# Spec theorem for `spqr::v1::unchunked::send_ek::serialize::EkSentCt1Received::into_pb`

Converts an `EkSentCt1Received` state from the in-memory Rust form
(`spqr::v1::unchunked::send_ek::EkSentCt1Received`) into the protobuf form
(`spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received`) used for saving it to disk.
The `epoch`, `dk` (decapsulation key) and `ct1` (first ciphertext) fields are copied over
unchanged and the `auth` field is converted with `Authenticator::into_pb` (a plain field copy)
and wrapped in `Some`. The result is pinned to the pure functional model
`FunctionalModels.intoPb`, which in turn calls the functional models of the component
conversions. The reverse direction is `from_pb`.

**Source**: spqr/src/v1/unchunked/send_ek/serialize.rs
-/

open Aeneas Aeneas.Std Result
namespace spqr.v1.unchunked.send_ek.serialize.EkSentCt1Received

/-- **Spec theorem for `spqr::v1::unchunked::send_ek::serialize::EkSentCt1Received::into_pb`**
• The call always succeeds (no panic).
• The extracted function agrees with its associated high-level functional model
  `FunctionalModels.intoPb` (see def).
-/
@[step]
theorem into_pb_spec (self : v1.unchunked.send_ek.EkSentCt1Received) :
    into_pb self ⦃ (result : proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received) =>
      result = FunctionalModels.intoPb self ⦄ := by
  unfold into_pb FunctionalModels.intoPb
  step*

end spqr.v1.unchunked.send_ek.serialize.EkSentCt1Received
