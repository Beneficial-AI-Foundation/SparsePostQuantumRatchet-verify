/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs
import Spqr.Auxiliary.Aeneas.TrySimps
import Spqr.Specs.Authenticator.Serialize.Authenticator.FromPb

/-! # Spec theorem for `spqr::v1::unchunked::send_ek::serialize::EkSent::from_pb`

Converts an `EkSent` state from the protobuf form
(`proto.pq_ratchet.v1_state.unchunked.EkSent`) back into the in-memory Rust
form (`v1.unchunked.send_ek.EkSent`). The decapsulation key `dk` must be
exactly 2400 bytes and the optional `auth` field must be present
(`Error::StateDecode` otherwise); `epoch` and `dk` are copied verbatim and
`auth` is converted with `Authenticator::from_pb` (a clone of the two key
vectors). The reverse direction is `into_pb`.

**Source**: src/v1/unchunked/send_ek/serialize.rs (lines 58:4-68:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.unchunked.send_ek.serialize.EkSent

/-- **Spec theorem for `v1.unchunked.send_ek.serialize.EkSent.from_pb`**:

• The call always succeeds (no panic).
• If `dk` is not 2400 bytes long or `pb.auth` is missing, the result is
  `Err Error.StateDecode`.
• Otherwise the result is `Ok` with `epoch` and `dk` copied verbatim and
  the `auth` key vectors preserved. -/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.v1_state.unchunked.EkSent) :
    from_pb pb ⦃ (result : core.result.Result v1.unchunked.send_ek.EkSent Error) =>
      if pb.dk.length = 2400 then
        match pb.auth with
        | none => result = .Err Error.StateDecode
        | some a => ∃ st, result = .Ok st ∧
            st.epoch = pb.epoch ∧
            st.dk = pb.dk ∧
            st.auth.root_key = a.root_key ∧
            st.auth.mac_key = a.mac_key
      else result = .Err Error.StateDecode ⦄ := by
  unfold from_pb
  by_cases hdk : pb.dk.length = 2400
  · rw [if_pos (by scalar_tac : alloc.vec.Vec.len pb.dk = 2400#usize)]
    simp only [hdk, reduceIte]
    match pb.auth with
    | none => simp only [spqr_try_simps]
    | some a =>
      simp only [spqr_try_simps]
      step*
  · rw [if_neg (by scalar_tac : ¬alloc.vec.Vec.len pb.dk = 2400#usize)]
    simp only [hdk, reduceIte, WP.spec_ok]

end spqr.v1.unchunked.send_ek.serialize.EkSent
