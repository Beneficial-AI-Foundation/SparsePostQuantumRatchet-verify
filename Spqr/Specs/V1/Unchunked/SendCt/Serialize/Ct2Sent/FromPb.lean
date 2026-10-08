/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang, Markus Dablander
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Serialize.Authenticator.FromPb
import Spqr.Specs.V1.Unchunked.SendCt.Serialize.Ct2Sent.FunctionalModels

/-!
# Spec theorem for `spqr::v1::unchunked::send_ct::serialize::Ct2Sent::from_pb`

Converts a `Ct2Sent` state from the protobuf form
(`spqr::proto::pq_ratchet::v1_state::unchunked::Ct2Sent`) back into the in-memory Rust
form (`spqr::v1::unchunked::send_ct::Ct2Sent`). The `epoch` field is copied over
unchanged; the optional `auth` field must be present (`Error::StateDecode` otherwise) and is
converted with `Authenticator::from_pb`. The result is pinned to the pure functional model
`FunctionalModels.fromPb`, which in turn calls the functional model of the `Authenticator`
conversion. The reverse direction is `into_pb`.

**Source**: spqr/src/v1/unchunked/send_ct/serialize.rs
-/

open Aeneas Aeneas.Std Result
namespace spqr.v1.unchunked.send_ct.serialize.Ct2Sent

/-- **Spec theorem for `spqr::v1::unchunked::send_ct::serialize::Ct2Sent::from_pb`**
• The call always succeeds (no panic).
• The extracted function agrees with its associated high-level functional model
  `FunctionalModels.fromPb` (see def).
-/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.v1_state.unchunked.Ct2Sent) :
    from_pb pb ⦃ (result : core.result.Result v1.unchunked.send_ct.Ct2Sent Error) =>
      result = FunctionalModels.fromPb pb ⦄ := by
  unfold from_pb FunctionalModels.fromPb
  rcases pb with ⟨_, _ | _⟩ <;> step* <;> simp_all

end spqr.v1.unchunked.send_ct.serialize.Ct2Sent
