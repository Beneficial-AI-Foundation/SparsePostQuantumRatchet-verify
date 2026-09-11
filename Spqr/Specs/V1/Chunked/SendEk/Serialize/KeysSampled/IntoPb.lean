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
  `PolyEncoder::into_pb` at `self.sending_hdr`: `2 * len + 2 ≤ Usize.max` per serialized item.
• Converting the chunking part succeeds: `PolyEncoder.into_pb self.sending_hdr = ok pe`. That
  fixes `pe` uniquely (but opaquely to mitigate excess verbosity in the theorem formulation).
• The result is pinned down completely: `epoch`, `ek`, `dk` come verbatim from `self.uc`,
  `root_key` and `mac_key` from `self.uc.auth`, `sending_hdr` is `pe`; the optional fields
  `uc`, `auth` and `sending_hdr` are all `some`.
-/
@[step]
theorem into_pb_spec (self : v1.chunked.send_ek.KeysSampled)
    (h_overflow_points : ∀ points, self.sending_hdr.s = .Points points →
      ∀ j < points.length, 2 * points[j]!.value.length + 2 ≤ Usize.max)
    (h_overflow_polys : ∀ polys, self.sending_hdr.s = .Polys polys →
      ∀ j < polys.length, 2 * polys[j]!.degree + 2 ≤ Usize.max) :
    into_pb self ⦃ (result : proto.pq_ratchet.v1_state.chunked.KeysSampled) =>
      ∃ pe, PolyEncoder.into_pb self.sending_hdr = ok pe ∧
      result = { uc := some { epoch := self.uc.epoch,
                              auth := some { root_key := self.uc.auth.root_key,
                                             mac_key := self.uc.auth.mac_key },
                              ek := self.uc.ek, dk := self.uc.dk },
                 sending_hdr := some pe } ⦄ := by
  unfold into_pb
  obtain ⟨pe, h_pe, -⟩ := spec_imp_exists (PolyEncoder.into_pb_spec self.sending_hdr ‹_› ‹_›)
  rw [h_pe]
  step*
  simp only [← hs_post1, ← hs_post2, ← hs_post3, ← hs_post4]

end spqr.v1.chunked.send_ek.serialize.KeysSampled
