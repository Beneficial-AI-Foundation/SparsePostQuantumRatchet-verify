/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Serialize.Authenticator.FromPb
import Spqr.Specs.V1.Unchunked.SendEk.Serialize.KeysUnsampled.FunctionalModels

/-! # Spec theorem for `spqr::v1::unchunked::send_ek::serialize::KeysUnsampled::from_pb`

Converts a `KeysUnsampled` state from the protobuf form
(`proto.pq_ratchet.v1_state.unchunked.KeysUnsampled`) back into the
in-memory Rust form (`v1.unchunked.send_ek.KeysUnsampled`). The `epoch`
field is copied over unchanged; the optional `auth` field must be present
(`Error::StateDecode` otherwise) and is converted with
`Authenticator::from_pb` (a clone of the two key vectors). The reverse
direction is `into_pb`.

**Source**: src/v1/unchunked/send_ek/serialize.rs (lines 17:4-22:5)
-/

open Aeneas Aeneas.Std Result
namespace spqr.v1.unchunked.send_ek.serialize.KeysUnsampled

/-- **Spec theorem for `v1.unchunked.send_ek.serialize.KeysUnsampled.from_pb`**:
• The call always succeeds (no panic).
• The result is exactly the functional model `FunctionalModels.fromPb pb`. -/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.v1_state.unchunked.KeysUnsampled) :
    from_pb pb ⦃ (result : core.result.Result v1.unchunked.send_ek.KeysUnsampled Error) =>
      result = FunctionalModels.fromPb pb ⦄ := by
  unfold from_pb FunctionalModels.fromPb
  match pb.auth with
  | none => step* <;> simp_all
  | some a' =>
    step* <;> simp_all [authenticator.serialize.Authenticator.FunctionalModels.fromPb]

end spqr.v1.unchunked.send_ek.serialize.KeysUnsampled
