/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Unchunked.SendEk.Serialize.KeysUnsampled.FromPb

/-!
# Spec theorem for `spqr::v1::chunked::send_ek::serialize::KeysUnsampled::from_pb`

Converts a chunked `KeysUnsampled` state from the protobuf form
(`spqr::proto::pq_ratchet::v1_state::chunked::KeysUnsampled`), as read back from disk, into
the in-memory Rust form (`spqr::v1::chunked::send_ek::KeysUnsampled`). The chunked state just
wraps a single unchunked field `uc`, but the corresponding protobuf field is optional, so it
must be present (`Error::StateDecode` otherwise). The conversion then delegates to the
unchunked `KeysUnsampled::from_pb`, which copies `epoch` verbatim and likewise requires its
optional `auth` field to be present (`Error::StateDecode` otherwise), converting it with
`Authenticator::from_pb` (a clone of the two key vectors `root_key` and `mac_key`). No
length validation is performed on either key vector here.

**Source:** "src/v1/chunked/send_ek/serialize.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace spqr.v1.chunked.send_ek.serialize.KeysUnsampled

/-- **Spec theorem for `spqr::v1::chunked::send_ek::serialize::KeysUnsampled::from_pb`**
• The call always succeeds (no panic).
• If `pb.uc` is missing, the result is `Err Error.StateDecode`.
• If `pb.uc` is present but its `auth` field is missing, the result is also
  `Err Error.StateDecode`.
• Otherwise the result is `Ok` with `epoch` and the `auth` key vectors `root_key` and
  `mac_key` copied verbatim; no length validation is performed on either key vector here.
-/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.v1_state.chunked.KeysUnsampled) :
    from_pb pb ⦃ (result : core.result.Result v1.chunked.send_ek.KeysUnsampled Error) =>
      match pb.uc with
      | none => result = .Err Error.StateDecode
      | some u =>
        match u.auth with
        | none => result = .Err Error.StateDecode
        | some a =>
          result = .Ok {
            uc := { epoch := u.epoch,
                    auth := { root_key := a.root_key, mac_key := a.mac_key } } } ⦄ := by
  unfold from_pb
  step* <;> grind

end spqr.v1.chunked.send_ek.serialize.KeysUnsampled
