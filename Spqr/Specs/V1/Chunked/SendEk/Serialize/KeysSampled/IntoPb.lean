/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Unchunked.SendEk.Serialize.HeaderSent.IntoPb
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.IntoPb

/-!
# Spec theorem for `spqr::v1::chunked::send_ek::serialize::KeysSampled::into_pb`

Converts a chunked `KeysSampled` state from its in-memory Rust form
(`spqr::v1::chunked::send_ek::KeysSampled`) into the protobuf form
(`spqr::proto::pq_ratchet::v1_state::chunked::KeysSampled`) used for saving it to disk.
The chunked state has two fields, each converted separately and wrapped in `Some` since the
corresponding protobuf fields are optional. The unchunked part `uc` is converted with
`HeaderSent::into_pb`, which copies `epoch`, `ek` and `dk` verbatim and converts `auth` with
`Authenticator::into_pb`, which copies `root_key` and `mac_key`. The chunking part `sending_hdr`
is converted with `PolyEncoder::into_pb`. That copies the chunk counter `idx` unchanged and turns
the numbers the encoder is holding into raw bytes: each number fits in 16 bits and is written as
two bytes, larger half first. The encoder is always in exactly one of two states, and only the
matching protobuf list is filled, a `Points` encoder writes into `pts` and leaves `polys` empty,
a `Polys` encoder writes into `polys` and leaves `pts` empty.

**Source:** "src/v1/chunked/send_ek/serialize.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open spqr.encoding.polynomial
namespace spqr.v1.chunked.send_ek.serialize.KeysSampled

/-- **Spec theorem for `spqr::v1::chunked::send_ek::serialize::KeysSampled::into_pb`**
• The call succeeds (no panic) given the two overflow hypotheses inherited from
  `PolyEncoder::into_pb` for `self.sending_hdr`: `2 * len + 2 ≤ Usize.max` per serialized item.
• Both optional protobuf fields of the result are always populated; the `| _ => False` branch
  rules out `none` in either position.
• The unchunked part `uc_pb` is pinned down as an explicit record literal copied from `self.uc`.
• The chunking part `hdr_pb` is pinned down at the detailed value level by
  `PolyEncoder.IntoPbPostCond self.sending_hdr hdr_pb`. -/
@[step]
theorem into_pb_spec (self : v1.chunked.send_ek.KeysSampled)
    (h_overflow_points : ∀ points, self.sending_hdr.s = .Points points →
      ∀ j < points.length, 2 * points[j]!.value.length + 2 ≤ Usize.max)
    (h_overflow_polys : ∀ polys, self.sending_hdr.s = .Polys polys →
      ∀ j < polys.length, 2 * polys[j]!.degree + 2 ≤ Usize.max) :
    into_pb self ⦃ (result : proto.pq_ratchet.v1_state.chunked.KeysSampled) =>
      match result with
      | { uc := some uc_pb, sending_hdr := some hdr_pb } =>
          uc_pb = { epoch := self.uc.epoch,
                    auth := some { root_key := self.uc.auth.root_key,
                                   mac_key := self.uc.auth.mac_key },
                    ek := self.uc.ek, dk := self.uc.dk } ∧
          PolyEncoder.IntoPbPostCond self.sending_hdr hdr_pb
      | _ => False ⦄ := by
  unfold into_pb
  obtain ⟨hdr_pb, h_hdr_pb, h_hdr_pb_post⟩ := spec_imp_exists
    (PolyEncoder.into_pb_spec self.sending_hdr h_overflow_points h_overflow_polys)
  rw [h_hdr_pb]
  step*
  refine ⟨?_, h_hdr_pb_post⟩
  simp only [← hs_post1, ← hs_post2, ← hs_post3, ← hs_post4]

end spqr.v1.chunked.send_ek.serialize.KeysSampled
