/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Serialize.Authenticator.FromPb

/-! # Spec theorem for `spqr::v1::unchunked::send_ct::serialize::HeaderReceived::from_pb`

Converts a `HeaderReceived` state from the protobuf form
(`proto.pq_ratchet.v1_state.unchunked.HeaderReceived`) back into the
in-memory Rust form (`v1.unchunked.send_ct.HeaderReceived`). The header
`hdr` must be exactly 64 bytes and the optional `auth` field must be
present (`Error::StateDecode` otherwise); `epoch` and `hdr` are copied
verbatim and `auth` is converted with `Authenticator::from_pb` (a clone
of the two key vectors). The reverse direction is `into_pb`.

**Source**: src/v1/unchunked/send_ct/serialize.rs (lines 34:4-44:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.unchunked.send_ct.serialize.HeaderReceived

/-- **Spec theorem for `v1.unchunked.send_ct.serialize.HeaderReceived.from_pb`**:

• The call always succeeds (no panic).
• If `hdr` is not 64 bytes long or `pb.auth` is missing, the result is
  `Err Error.StateDecode`.
• Otherwise the result is `Ok` with `epoch` and `hdr` copied verbatim and
  the `auth` key vectors preserved. -/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.v1_state.unchunked.HeaderReceived) :
    from_pb pb ⦃ (result : core.result.Result v1.unchunked.send_ct.HeaderReceived Error) =>
      if pb.hdr.length = 64 then
        match pb.auth with
        | none => result = .Err Error.StateDecode
        | some a =>
          result = .Ok {
            epoch := pb.epoch,
            auth := { root_key := a.root_key, mac_key := a.mac_key },
            hdr := pb.hdr }
      else result = .Err Error.StateDecode ⦄ := by
  unfold from_pb
  by_cases hhdr : pb.hdr.length = 64
  · rw [if_pos (by scalar_tac : alloc.vec.Vec.len pb.hdr = 64#usize)]
    simp only [hhdr, reduceIte]
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
  · rw [if_neg (by scalar_tac : ¬alloc.vec.Vec.len pb.hdr = 64#usize)]
    simp [hhdr, WP.spec_ok]

end spqr.v1.unchunked.send_ct.serialize.HeaderReceived
