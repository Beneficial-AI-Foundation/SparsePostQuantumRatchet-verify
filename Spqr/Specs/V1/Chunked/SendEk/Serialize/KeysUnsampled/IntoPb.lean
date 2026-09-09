/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Unchunked.SendEk.Serialize.KeysUnsampled.IntoPb

/-!
# Spec theorem for `spqr::v1::chunked::send_ek::serialize::KeysUnsampled::into_pb`

Converts a chunked `KeysUnsampled` state from its in-memory Rust form
(`spqr::v1::chunked::send_ek::KeysUnsampled`) into the protobuf form
(`spqr::proto::pq_ratchet::v1_state::chunked::KeysUnsampled`) used for saving it to disk.
The chunked state just wraps a single unchunked field `uc`, so the conversion delegates to
the unchunked `KeysUnsampled::into_pb` and wraps its result in `Some`, since the protobuf
field is optional. The unchunked conversion copies `epoch` verbatim and converts `auth` with
`Authenticator::into_pb`, which copies `root_key` and `mac_key`. The reverse direction is
`from_pb`.

**Source:** "src/v1/chunked/send_ek/serialize.rs"
-/

open Aeneas Aeneas.Std Result
namespace spqr.v1.chunked.send_ek.serialize.KeysUnsampled

/-- **Spec theorem for `spqr::v1::chunked::send_ek::serialize::KeysUnsampled::into_pb`**
• The call always succeeds (no panic).
• The result is pinned down completely: `epoch`, `root_key` and `mac_key` are copied
  verbatim from `self.uc`, each of the two optional wrapper fields being `some`.
-/
@[step]
theorem into_pb_spec (self : v1.chunked.send_ek.KeysUnsampled) :
    into_pb self ⦃ (result : proto.pq_ratchet.v1_state.chunked.KeysUnsampled) =>
      result = { uc := some { epoch := self.uc.epoch,
                              auth := some { root_key := self.uc.auth.root_key,
                                             mac_key := self.uc.auth.mac_key } } } ⦄ := by
  unfold into_pb
  step*
  simp only [← ku_post1, ← ku_post2]

end spqr.v1.chunked.send_ek.serialize.KeysUnsampled
