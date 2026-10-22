/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang, Markus Dablander
-/
module

public import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Serialize.Authenticator.FromPb
public import Spqr.Specs.V1.Unchunked.SendCt.Serialize.Ct1SentEkReceived.FunctionalModels

/-!
# Spec theorem for `spqr::v1::unchunked::send_ct::serialize::Ct1SentEkReceived::from_pb`

Converts a `Ct1SentEkReceived` state from the protobuf form
(`spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived`) back into the in-memory
Rust form (`spqr::v1::unchunked::send_ct::Ct1SentEkReceived`). The encapsulation state `es`
must be exactly 2080 bytes long, the first ciphertext `ct1` exactly 960 bytes long, the
encapsulation key `ek` exactly 1152 bytes long and the optional `auth` field must be present
(`Error::StateDecode` otherwise); `epoch`, `es`, `ek` and `ct1` are copied over unchanged and
`auth` is converted with `Authenticator::from_pb`. The result is pinned to the pure functional
model `FunctionalModels.fromPb`, which in turn calls the functional models of the component
conversions. The reverse direction is `into_pb`.

**Source**: spqr/src/v1/unchunked/send_ct/serialize.rs
-/

@[expose] public section

open Aeneas Aeneas.Std Result
namespace spqr.v1.unchunked.send_ct.serialize.Ct1SentEkReceived

/-- **Spec theorem for `spqr::v1::unchunked::send_ct::serialize::Ct1SentEkReceived::from_pb`**
• The call always succeeds (no panic).
• The extracted function agrees with its associated high-level functional model
  `FunctionalModels.fromPb` (see def).
-/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived) :
    from_pb pb ⦃ (result : core.result.Result v1.unchunked.send_ct.Ct1SentEkReceived Error) =>
      result = FunctionalModels.fromPb pb ⦄ := by
  unfold from_pb FunctionalModels.fromPb
  by_cases hes : pb.es.length = 2080
  · rw [ite_eq_left (by scalar_tac : alloc.vec.Vec.len pb.es = 2080#usize), hes]
    by_cases hct1 : pb.ct1.length = 960
    · rw [ite_eq_left (by scalar_tac : alloc.vec.Vec.len pb.ct1 = 960#usize), hct1]
      by_cases hek : pb.ek.length = 1152
      · rw [ite_eq_left (by scalar_tac : alloc.vec.Vec.len pb.ek = 1152#usize), hek]
        rcases pb with ⟨_, _ | _, _, _, _⟩ <;> step* <;> simp_all
      · rw [ite_eq_right (by scalar_tac : ¬ alloc.vec.Vec.len pb.ek = 1152#usize)]
        step*
        simp_all
    · rw [ite_eq_right (by scalar_tac : ¬ alloc.vec.Vec.len pb.ct1 = 960#usize)]
      step*
      simp_all
  · rw [ite_eq_right (by scalar_tac : ¬ alloc.vec.Vec.len pb.es = 2080#usize)]
    step*
    simp_all

end spqr.v1.unchunked.send_ct.serialize.Ct1SentEkReceived
