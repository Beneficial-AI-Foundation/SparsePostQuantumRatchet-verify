/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Serialize.Authenticator.FromPb

/-! # Spec theorem for `spqr::v1::unchunked::send_ct::serialize::NoHeaderReceived::from_pb`

Converts a `NoHeaderReceived` state from the protobuf form
(`proto.pq_ratchet.v1_state.unchunked.NoHeaderReceived`) read from disk
back into the in-memory Rust form (`v1.unchunked.send_ct.NoHeaderReceived`).
The `epoch` field is copied over unchanged; the `auth` field must be
present (`Some`) and is converted with `Authenticator::from_pb` (a plain
field copy), otherwise the function returns `Err(Error::StateDecode)`.
The reverse direction is `into_pb`.

**Source**: src/v1/unchunked/send_ct/serialize.rs (lines 17:4-22:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.unchunked.send_ct.serialize.NoHeaderReceived

/-- **Spec theorem for `v1.unchunked.send_ct.serialize.NoHeaderReceived.from_pb`**:

• The call always succeeds (no panic) and never returns a spurious error.
• If `pb.auth` is missing, the result is `Err Error.StateDecode`.
• If `pb.auth = some a`, the result is `Ok` of the state with `epoch`
  copied from `pb` and `auth` carrying the same `root_key` and `mac_key`
  as `a`. -/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.v1_state.unchunked.NoHeaderReceived) :
    from_pb pb ⦃ (result : core.result.Result v1.unchunked.send_ct.NoHeaderReceived Error) =>
      match pb.auth with
      | none => result = .Err Error.StateDecode
      | some a => result = .Ok { epoch := pb.epoch,
                                 auth := { root_key := a.root_key,
                                           mac_key := a.mac_key } } ⦄ := by
  unfold from_pb
  match pb.auth with
  | none =>
    simp [core.option.Option.as_ref, core.option.Option.ok_or,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from]
  | some pa =>
    simp only [core.option.Option.as_ref, core.option.Option.ok_or,
               core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
    step*
    obtain ⟨root_key, mac_key⟩ := a
    simp_all

end spqr.v1.unchunked.send_ct.serialize.NoHeaderReceived
