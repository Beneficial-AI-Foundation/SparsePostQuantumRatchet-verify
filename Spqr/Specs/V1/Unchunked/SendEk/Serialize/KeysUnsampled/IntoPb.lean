/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs

/-! # Spec theorem for `spqr::v1::unchunked::send_ek::serialize::KeysUnsampled::into_pb`

Converts a `KeysUnsampled` state from the in-memory Rust form
(`v1.unchunked.send_ek.KeysUnsampled`) into the protobuf form
(`proto.pq_ratchet.v1_state.unchunked.KeysUnsampled`) used for saving it to
disk. The `epoch` field is copied over unchanged and the `auth` field is
converted with `Authenticator::into_pb` (a plain field copy) and wrapped in
`Some`. The reverse direction is `from_pb`.

**Source**: src/v1/unchunked/send_ek/serialize.rs (lines 10:4-15:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.unchunked.send_ek.serialize.KeysUnsampled

/-- **Spec theorem for `v1.unchunked.send_ek.serialize.KeysUnsampled.into_pb`**:

• The call always succeeds (no panic).
• The result's `epoch` equals `self.epoch`.
• The result's `auth` is `some` of the protobuf form of `self.auth`,
  carrying the same `root_key` and `mac_key`. -/
@[step]
theorem into_pb_spec (self : v1.unchunked.send_ek.KeysUnsampled) :
    into_pb self ⦃ (result : proto.pq_ratchet.v1_state.unchunked.KeysUnsampled) =>
      result.epoch = self.epoch ∧
      result.auth = some { root_key := self.auth.root_key,
                           mac_key := self.auth.mac_key } ⦄ := by
  simp [into_pb, authenticator.serialize.Authenticator.into_pb]

end spqr.v1.unchunked.send_ek.serialize.KeysUnsampled
