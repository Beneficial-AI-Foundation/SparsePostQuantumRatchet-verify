/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs

/-! # Spec theorem for `spqr::v1::unchunked::send_ek::serialize::HeaderSent::into_pb`

Converts a `HeaderSent` state from the in-memory Rust form
(`v1.unchunked.send_ek.HeaderSent`) into the protobuf form
(`proto.pq_ratchet.v1_state.unchunked.HeaderSent`) used for saving it to
disk. The `epoch`, `ek` (encapsulation key) and `dk` (decapsulation key)
fields are copied over unchanged and the `auth` field is converted with
`Authenticator::into_pb` (a plain field copy) and wrapped in `Some`. The
reverse direction is `from_pb`.

**Source**: src/v1/unchunked/send_ek/serialize.rs (lines 26:4-33:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.unchunked.send_ek.serialize.HeaderSent

/-- **Spec theorem for `v1.unchunked.send_ek.serialize.HeaderSent.into_pb`**:

• The call always succeeds (no panic).
• The result's `epoch`, `ek` and `dk` equal the corresponding fields of `self`.
• The result's `auth` is `some` of the protobuf form of `self.auth`,
  carrying the same `root_key` and `mac_key`. -/
@[step]
theorem into_pb_spec (self : v1.unchunked.send_ek.HeaderSent) :
    into_pb self ⦃ (result : proto.pq_ratchet.v1_state.unchunked.HeaderSent) =>
      result.epoch = self.epoch ∧
      result.ek = self.ek ∧
      result.dk = self.dk ∧
      result.auth = some { root_key := self.auth.root_key,
                           mac_key := self.auth.mac_key } ⦄ := by
  simp [into_pb, authenticator.serialize.Authenticator.into_pb]

end spqr.v1.unchunked.send_ek.serialize.HeaderSent
