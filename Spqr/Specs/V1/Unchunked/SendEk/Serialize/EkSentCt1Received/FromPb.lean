/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang, Markus Dablander
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Serialize.Authenticator.FromPb
import Spqr.Specs.V1.Unchunked.SendEk.Serialize.EkSentCt1Received.FunctionalModels

/-!
# Spec theorem for `spqr::v1::unchunked::send_ek::serialize::EkSentCt1Received::from_pb`

Converts an `EkSentCt1Received` state from the protobuf form
(`spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received`) back into the in-memory
Rust form (`spqr::v1::unchunked::send_ek::EkSentCt1Received`). The decapsulation key `dk` must
be exactly 2400 bytes long, the first ciphertext `ct1` exactly 960 bytes long and the optional
`auth` field must be present (`Error::StateDecode` otherwise); `epoch`, `dk` and `ct1` are
copied over unchanged and `auth` is converted with `Authenticator::from_pb`. The result is
pinned to the pure functional model `FunctionalModels.fromPb`, which in turn calls the
functional models of the component conversions. The reverse direction is `into_pb`.

**Source**: spqr/src/v1/unchunked/send_ek/serialize.rs
-/

open Aeneas Aeneas.Std Result
namespace spqr.v1.unchunked.send_ek.serialize.EkSentCt1Received

/-- **Spec theorem for `spqr::v1::unchunked::send_ek::serialize::EkSentCt1Received::from_pb`**
• The call always succeeds (no panic).
• The extracted function agrees with its associated high-level functional model
  `FunctionalModels.fromPb` (see def).
-/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received) :
    from_pb pb ⦃ (result : core.result.Result v1.unchunked.send_ek.EkSentCt1Received Error) =>
      result = FunctionalModels.fromPb pb ⦄ := by
  unfold from_pb FunctionalModels.fromPb
  by_cases hdk : pb.dk.length = 2400
  · rw [if_pos (by scalar_tac : alloc.vec.Vec.len pb.dk = 2400#usize), hdk]
    by_cases hct1 : pb.ct1.length = 960
    · rw [if_pos (by scalar_tac : alloc.vec.Vec.len pb.ct1 = 960#usize), hct1]
      rcases pb with ⟨_, _ | _, _, _⟩ <;> step* <;> simp_all
    · rw [if_neg (by scalar_tac : ¬ alloc.vec.Vec.len pb.ct1 = 960#usize)]
      step*
      simp_all
  · rw [if_neg (by scalar_tac : ¬ alloc.vec.Vec.len pb.dk = 2400#usize)]
    step*
    simp_all

end spqr.v1.unchunked.send_ek.serialize.EkSentCt1Received
