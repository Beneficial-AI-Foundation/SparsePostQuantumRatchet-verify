/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Serialize.Authenticator.FromPb

/-! # Spec theorem for `spqr::v1::unchunked::send_ek::serialize::EkSentCt1Received::from_pb`

Converts an `EkSentCt1Received` state from the protobuf form
(`proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received`) back into the
in-memory Rust form (`v1.unchunked.send_ek.EkSentCt1Received`). The
decapsulation key `dk` must be exactly 2400 bytes, the first ciphertext
`ct1` exactly 960 bytes, and the optional `auth` field must be present
(`Error::StateDecode` otherwise); `epoch`, `dk` and `ct1` are copied
verbatim and `auth` is converted with `Authenticator::from_pb` (a clone of
the two key vectors). The reverse direction is `into_pb`.

**Source**: src/v1/unchunked/send_ek/serialize.rs (lines 81:4-92:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.unchunked.send_ek.serialize.EkSentCt1Received

/-- **Spec theorem for `v1.unchunked.send_ek.serialize.EkSentCt1Received.from_pb`**:

• The call always succeeds (no panic).
• If `dk` is not 2400 bytes long, `ct1` is not 960 bytes long, or `pb.auth`
  is missing, the result is `Err Error.StateDecode`.
• Otherwise the result is `Ok` with `epoch`, `dk` and `ct1` copied verbatim
  and the `auth` key vectors preserved. -/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received) :
    from_pb pb ⦃ (result : core.result.Result v1.unchunked.send_ek.EkSentCt1Received Error) =>
      if pb.dk.length = 2400 ∧ pb.ct1.length = 960 then
        match pb.auth with
        | none => result = .Err Error.StateDecode
        | some a => ∃ st, result = .Ok st ∧
            st.epoch = pb.epoch ∧
            st.dk = pb.dk ∧
            st.ct1 = pb.ct1 ∧
            st.auth.root_key = a.root_key ∧
            st.auth.mac_key = a.mac_key
      else result = .Err Error.StateDecode ⦄ := by
  unfold from_pb
  by_cases hdk : pb.dk.length = 2400
  · rw [if_pos (by scalar_tac : alloc.vec.Vec.len pb.dk = 2400#usize)]
    by_cases hct : pb.ct1.length = 960
    · rw [if_pos (by scalar_tac : alloc.vec.Vec.len pb.ct1 = 960#usize)]
      simp only [hdk, hct, and_self, reduceIte]
      match pb.auth with
      | none =>
        simp only [core.option.Option.as_ref, core.option.Option.ok_or,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
      | some a =>
        simp only [core.option.Option.as_ref, core.option.Option.ok_or,
          core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
        step*
    · rw [if_neg (by scalar_tac : ¬alloc.vec.Vec.len pb.ct1 = 960#usize)]
      simp [hct, WP.spec_ok]
  · rw [if_neg (by scalar_tac : ¬alloc.vec.Vec.len pb.dk = 2400#usize)]
    simp [hdk, WP.spec_ok]

end spqr.v1.unchunked.send_ek.serialize.EkSentCt1Received
