/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Unchunked.SendEk.Serialize.HeaderSent.FromPb
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.FromPb

/-!
# Spec theorem for `spqr::v1::chunked::send_ek::serialize::KeysSampled::from_pb`

Converts a chunked `KeysSampled` state from the protobuf form
(`spqr::proto::pq_ratchet::v1_state::chunked::KeysSampled`), as read back from disk, into the
in-memory Rust form (`spqr::v1::chunked::send_ek::KeysSampled`). The chunked state has two
fields, `uc` and `sending_hdr`, and the corresponding protobuf fields are both optional, so each
must be present (`Error::StateDecode` otherwise). The unchunked part `uc` is converted with
`HeaderSent::from_pb`, which requires the decapsulation key `dk` to be exactly 2400 bytes, the
encapsulation key `ek` to be exactly 1152 bytes, and the optional `auth` field to be present
(`Error::StateDecode` otherwise); `epoch`, `ek` and `dk` are copied verbatim and `auth` is
converted with `Authenticator::from_pb` (a clone of the two key vectors `root_key` and `mac_key`).
The chunking part `sending_hdr` is converted with `PolyEncoder::from_pb`, which copies the chunk
counter `idx` and rebuilds the encoder from exactly one of the two protobuf byte lists: either
`pts` is empty and `polys` holds 16 nonempty even-length entries, or `polys` is empty and `pts`
holds 16 even-length entries. Any other shape is a `PolynomialError`, which is mapped to
`Error::StateDecode`. Every failure path of this function therefore yields `Error::StateDecode`.

**Source:** "src/v1/chunked/send_ek/serialize.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open spqr.encoding.polynomial
namespace spqr.v1.chunked.send_ek.serialize.KeysSampled

/-- **Spec theorem for `spqr::v1::chunked::send_ek::serialize::KeysSampled::from_pb`**
• The call always succeeds (no panic).
• If `pb.uc` is missing, the result is `Err Error.StateDecode`.
• If `pb.uc` is present but its `dk` is not 2400 bytes long, its `ek` is not 1152 bytes long, or
  its `auth` field is missing, the result is `Err Error.StateDecode`.
• If `pb.sending_hdr` is missing, or is present but not accepted by `PolyEncoder::from_pb`
  (`PolyEncoder.FromPbWellFormed` fails), the result is `Err Error.StateDecode`.
• Otherwise the result is `Ok` with the unchunked part `uc` pinned down as an explicit record
  literal (`epoch`, `ek` and `dk` copied verbatim, the `auth` key vectors `root_key` and
  `mac_key` preserved) and the chunking part `sending_hdr` pinned down at the detailed value
  level by `PolyEncoder.IntoPbPostCond`, i.e. the decoded encoder serialises back to
  `pb.sending_hdr`.
-/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.v1_state.chunked.KeysSampled) :
    from_pb pb ⦃ (result : core.result.Result v1.chunked.send_ek.KeysSampled Error) =>
      match pb.uc with
      | none => result = .Err Error.StateDecode
      | some u =>
        if u.dk.length = 2400 ∧ u.ek.length = 1152 then
          match u.auth with
          | none => result = .Err Error.StateDecode
          | some a =>
            match pb.sending_hdr with
            | none => result = .Err Error.StateDecode
            | some hdr_pb =>
              if PolyEncoder.FromPbWellFormed hdr_pb then
                match result with
                | .Ok ks =>
                  ks.uc = { epoch := u.epoch,
                            auth := { root_key := a.root_key, mac_key := a.mac_key },
                            ek := u.ek, dk := u.dk } ∧
                  PolyEncoder.IntoPbPostCond ks.sending_hdr hdr_pb
                | .Err _ => False
              else result = .Err Error.StateDecode
        else result = .Err Error.StateDecode ⦄ := by
  unfold from_pb
  have h_map_err (r : core.result.Result PolyEncoder PolynomialError) :
      core.result.Result.map_err
        from_pb.closure.Insts.CoreOpsFunctionFnOnceTuplePolynomialErrorError r () ⦃ res =>
        res = match r with | .Ok v => .Ok v | .Err _ => .Err Error.StateDecode ⦄ := by
    rcases r with v | e <;> rfl
  step*
  · simp only [PolyEncoder.FromPbPostCond] at r3_post
    grind
  · simp only [PolyEncoder.FromPbPostCond] at r3_post
    grind
  · grind
  · grind
  · grind

end spqr.v1.chunked.send_ek.serialize.KeysSampled
