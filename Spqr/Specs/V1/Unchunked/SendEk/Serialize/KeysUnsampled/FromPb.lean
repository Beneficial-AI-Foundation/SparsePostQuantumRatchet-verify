/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs
import Spqr.Auxiliary.Aeneas.TrySimps
import Spqr.Specs.Authenticator.Serialize.Authenticator.FromPb

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
• If `pb.auth` is missing, the result is `Err Error.StateDecode`.
• Otherwise the result is `Ok` with `epoch` copied verbatim and the `auth`
  key vectors preserved. -/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.v1_state.unchunked.KeysUnsampled) :
    from_pb pb ⦃ (result : core.result.Result v1.unchunked.send_ek.KeysUnsampled Error) =>
      match pb.auth with
      | none => result = .Err Error.StateDecode
      | some a => ∃ st, result = .Ok st ∧
          st.epoch = pb.epoch ∧
          st.auth.root_key = a.root_key ∧
          st.auth.mac_key = a.mac_key ⦄ := by
  unfold from_pb
  match pb.auth with
  | none => simp only [spqr_try_simps]
  | some a =>
    simp only [spqr_try_simps]
    step*

end spqr.v1.unchunked.send_ek.serialize.KeysUnsampled
