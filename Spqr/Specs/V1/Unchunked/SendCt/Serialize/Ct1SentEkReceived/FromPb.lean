/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Serialize.Authenticator.FromPb

/-! # Spec theorem for `spqr::v1::unchunked::send_ct::serialize::Ct1SentEkReceived::from_pb`

Converts a `Ct1SentEkReceived` state from the protobuf form
(`proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived`) back into the
in-memory Rust form (`v1.unchunked.send_ct.Ct1SentEkReceived`). The
encapsulation randomness `es` must be exactly 2080 bytes, the first
ciphertext `ct1` exactly 960 bytes, the encapsulation key `ek` exactly
1152 bytes, and the optional `auth` field must be present
(`Error::StateDecode` otherwise); `epoch`, `es`, `ek` and `ct1` are copied
verbatim and `auth` is converted with `Authenticator::from_pb` (a clone of
the two key vectors). The reverse direction is `into_pb`.

**Source**: src/v1/unchunked/send_ct/serialize.rs (lines 84:4-96:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.unchunked.send_ct.serialize.Ct1SentEkReceived

/-- **Spec theorem for `v1.unchunked.send_ct.serialize.Ct1SentEkReceived.from_pb`**:

• The call always succeeds (no panic).
• If `es` is not 2080 bytes long, `ct1` is not 960 bytes long, `ek` is not
  1152 bytes long, or `pb.auth` is missing, the result is
  `Err Error.StateDecode`.
• Otherwise the result is `Ok` with `epoch`, `es`, `ek` and `ct1` copied
  verbatim and the `auth` key vectors preserved. -/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived) :
    from_pb pb ⦃ (result : core.result.Result v1.unchunked.send_ct.Ct1SentEkReceived Error) =>
      if pb.es.length = 2080 ∧ pb.ct1.length = 960 ∧ pb.ek.length = 1152 then
        match pb.auth with
        | none => result = .Err Error.StateDecode
        | some a =>
          result = .Ok {
            epoch := pb.epoch,
            auth := { root_key := a.root_key, mac_key := a.mac_key },
            es := pb.es, ek := pb.ek, ct1 := pb.ct1 }
      else result = .Err Error.StateDecode ⦄ := by
  unfold from_pb
  by_cases hes : pb.es.length = 2080
  · rw [if_pos (by scalar_tac : alloc.vec.Vec.len pb.es = 2080#usize)]
    by_cases hct : pb.ct1.length = 960
    · rw [if_pos (by scalar_tac : alloc.vec.Vec.len pb.ct1 = 960#usize)]
      by_cases hek : pb.ek.length = 1152
      · rw [if_pos (by scalar_tac : alloc.vec.Vec.len pb.ek = 1152#usize)]
        simp only [hes, hct, hek, and_self, reduceIte]
        match pb.auth with
        | none =>
          simp only [core.option.Option.as_ref, core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
        | some a' =>
          simp only [core.option.Option.as_ref, core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
          step*
          simp only [← a_post1, ← a_post2]
      · rw [if_neg (by scalar_tac : ¬alloc.vec.Vec.len pb.ek = 1152#usize)]
        simp [hek, WP.spec_ok]
    · rw [if_neg (by scalar_tac : ¬alloc.vec.Vec.len pb.ct1 = 960#usize)]
      simp [hct, WP.spec_ok]
  · rw [if_neg (by scalar_tac : ¬alloc.vec.Vec.len pb.es = 2080#usize)]
    simp [hes, WP.spec_ok]

end spqr.v1.unchunked.send_ct.serialize.Ct1SentEkReceived
