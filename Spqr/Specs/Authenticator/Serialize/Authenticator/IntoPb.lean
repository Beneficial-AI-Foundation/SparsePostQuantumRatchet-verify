/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Serialize.Authenticator.FunctionalModels

/-!
# Spec theorem for `spqr::authenticator::serialize::Authenticator::into_pb`

Converts an `Authenticator` from the in-memory Rust form (`spqr::authenticator::Authenticator`)
into the protobuf form (`spqr::proto::pq_ratchet::Authenticator`) used for sending it over the
network or saving it to disk. Both forms carry the same two byte-vector fields, `root_key` and
`mac_key`, so the conversion just hands those bytes over to the new struct. The result is pinned
to the pure functional model `FunctionalModels.intoPb`. The reverse direction is `from_pb`;
together the two functions let a value round-trip between the in-memory and protobuf forms
without losing information.

**Source**: spqr/src/authenticator/serialize.rs
-/

open Aeneas
namespace spqr.authenticator.serialize.Authenticator

/-- **Spec theorem for `spqr::authenticator::serialize::Authenticator::into_pb`**
• The call always succeeds (no panic).
• The extracted function agrees with its associated high-level functional model
  `FunctionalModels.intoPb` (see def).
-/
@[step]
theorem into_pb_spec (self : authenticator.Authenticator) :
    into_pb self ⦃ (result : proto.pq_ratchet.Authenticator) =>
      result = FunctionalModels.intoPb self ⦄ := by
  simp [into_pb, FunctionalModels.intoPb]

end spqr.authenticator.serialize.Authenticator
