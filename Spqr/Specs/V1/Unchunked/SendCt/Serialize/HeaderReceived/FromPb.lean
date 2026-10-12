/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang, Markus Dablander
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Authenticator.Serialize.Authenticator.FromPb
public import Spqr.Specs.V1.Unchunked.SendCt.Serialize.HeaderReceived.FunctionalModels

/-!
# Spec theorem for `spqr::v1::unchunked::send_ct::serialize::HeaderReceived::from_pb`

Converts a `HeaderReceived` state from the protobuf form
(`spqr::proto::pq_ratchet::v1_state::unchunked::HeaderReceived`) back into the in-memory
Rust form (`spqr::v1::unchunked::send_ct::HeaderReceived`). The header `hdr` must be exactly
64 bytes long and the optional `auth` field must be present (`Error::StateDecode` otherwise);
`epoch` and `hdr` are copied over unchanged and `auth` is converted with `Authenticator::from_pb`.
The result is pinned to the pure functional model `FunctionalModels.fromPb`, which in turn calls
the functional model of the `Authenticator` conversion. The reverse direction is `into_pb`.

**Source**: spqr/src/v1/unchunked/send_ct/serialize.rs
-/

@[expose] public section

open Aeneas Aeneas.Std Result
namespace spqr.v1.unchunked.send_ct.serialize.HeaderReceived

/-- **Spec theorem for `spqr::v1::unchunked::send_ct::serialize::HeaderReceived::from_pb`**
• The call always succeeds (no panic).
• The extracted function agrees with its associated high-level functional model
  `FunctionalModels.fromPb` (see def).
-/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.v1_state.unchunked.HeaderReceived) :
    from_pb pb ⦃ (result : core.result.Result v1.unchunked.send_ct.HeaderReceived Error) =>
      result = FunctionalModels.fromPb pb ⦄ := by
  unfold from_pb FunctionalModels.fromPb
  by_cases hl : pb.hdr.length = 64
  · rw [if_pos (by scalar_tac : alloc.vec.Vec.len pb.hdr = 64#usize), hl]
    rcases pb with ⟨_, _ | _, _⟩ <;> step* <;> simp_all
  · rw [if_neg (by scalar_tac : ¬ alloc.vec.Vec.len pb.hdr = 64#usize)]
    step*
    simp_all

end spqr.v1.unchunked.send_ct.serialize.HeaderReceived
