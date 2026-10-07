/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang, Markus Dablander
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Serialize.Authenticator.IntoPb
import Spqr.Specs.V1.Unchunked.SendCt.Serialize.NoHeaderReceived.FunctionalModels

/-!
# Spec theorem for `spqr::v1::unchunked::send_ct::serialize::NoHeaderReceived::into_pb`

Converts a `NoHeaderReceived` state from the in-memory Rust form
(`spqr::v1::unchunked::send_ct::NoHeaderReceived`) into the protobuf form
(`spqr::proto::pq_ratchet::v1_state::unchunked::NoHeaderReceived`) used for saving it to disk.
The `epoch` field is copied over unchanged and the `auth` field is converted with
`Authenticator::into_pb` (a plain field copy) and wrapped in `Some`. The result is pinned to the
pure functional model `FunctionalModels.intoPb`, which in turn calls the functional model of the
`Authenticator` conversion. The reverse direction is `from_pb`.

**Source**: spqr/src/v1/unchunked/send_ct/serialize.rs
-/

open Aeneas Aeneas.Std Result
namespace spqr.v1.unchunked.send_ct.serialize.NoHeaderReceived

/-- **Spec theorem for `spqr::v1::unchunked::send_ct::serialize::NoHeaderReceived::into_pb`**
• The call always succeeds (no panic).
• The extracted function agrees with its associated high-level functional model
  `FunctionalModels.intoPb` (see def).
-/
@[step]
theorem into_pb_spec (self : v1.unchunked.send_ct.NoHeaderReceived) :
    into_pb self ⦃ (result : proto.pq_ratchet.v1_state.unchunked.NoHeaderReceived) =>
      result = FunctionalModels.intoPb self ⦄ := by
  unfold into_pb FunctionalModels.intoPb
  step*

end spqr.v1.unchunked.send_ct.serialize.NoHeaderReceived
