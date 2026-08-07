/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Serialize.Authenticator.IntoPb

/-! # Spec theorem for `spqr::v1::unchunked::send_ct::serialize::Ct1SentEkReceived::into_pb`

Converts a `Ct1SentEkReceived` state from the in-memory Rust form
(`v1.unchunked.send_ct.Ct1SentEkReceived`) into the protobuf form
(`proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived`) used for saving
it to disk. The `epoch`, `es` and `ek` fields are copied over unchanged,
the `auth` field is converted with `Authenticator::into_pb` (a plain field
copy) and wrapped in `Some`, and `ct1` is cloned into a fresh vector with
`to_vec` (byte cloning is the identity, so its contents are preserved
exactly). The reverse direction is `from_pb`.

**Source**: src/v1/unchunked/send_ct/serialize.rs (lines 74:4-82:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.unchunked.send_ct.serialize.Ct1SentEkReceived

/-- **Spec theorem for `v1.unchunked.send_ct.serialize.Ct1SentEkReceived.into_pb`**:

• The call always succeeds (no panic).
• The result's `epoch`, `es`, `ek` and `ct1` equal the corresponding
  fields of `self` (cloning the `ct1` byte vector preserves it exactly).
• The result's `auth` is `some` of the protobuf form of `self.auth`,
  carrying the same `root_key` and `mac_key`. -/
@[step]
theorem into_pb_spec (self : v1.unchunked.send_ct.Ct1SentEkReceived) :
    into_pb self ⦃ (result : proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived) =>
      result.epoch = self.epoch ∧
      result.es = self.es ∧
      result.ek = self.ek ∧
      result.ct1 = self.ct1 ∧
      result.auth = some { root_key := self.auth.root_key,
                           mac_key := self.auth.mac_key } ⦄ := by
  unfold into_pb
  step*
  obtain ⟨root_key, mac_key⟩ := a
  simp_all [alloc.vec.Vec.deref]

end spqr.v1.unchunked.send_ct.serialize.Ct1SentEkReceived
