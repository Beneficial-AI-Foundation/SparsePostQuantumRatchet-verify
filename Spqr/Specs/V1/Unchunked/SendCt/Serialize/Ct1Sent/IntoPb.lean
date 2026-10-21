/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang, Markus Dablander
-/
module

public import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Serialize.Authenticator.IntoPb
public import Spqr.Specs.V1.Unchunked.SendCt.Serialize.Ct1Sent.FunctionalModels

/-!
# Spec theorem for `spqr::v1::unchunked::send_ct::serialize::Ct1Sent::into_pb`

Converts a `Ct1Sent` state from the in-memory Rust form
(`spqr::v1::unchunked::send_ct::Ct1Sent`) into the protobuf form
(`spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent`) used for saving it to disk.
The `epoch`, `hdr` and `es` fields are copied over unchanged, the `auth` field is converted with
`Authenticator::into_pb` (a plain field copy) and wrapped in `Some`, and `ct1` is cloned into a
fresh vector with `to_vec` (byte cloning is the identity, so its contents are preserved exactly).
The result is pinned to the pure functional model `FunctionalModels.intoPb`, which in turn calls
the functional models of the component conversions. The reverse direction is `from_pb`.

**Source**: spqr/src/v1/unchunked/send_ct/serialize.rs
-/

@[expose] public section

open Aeneas Aeneas.Std Result
namespace spqr.v1.unchunked.send_ct.serialize.Ct1Sent

/-- **Spec theorem for `spqr::v1::unchunked::send_ct::serialize::Ct1Sent::into_pb`**
• The call always succeeds (no panic).
• The extracted function agrees with its associated high-level functional model
  `FunctionalModels.intoPb` (see def).
-/
@[step]
theorem into_pb_spec (self : v1.unchunked.send_ct.Ct1Sent) :
    into_pb self ⦃ (result : proto.pq_ratchet.v1_state.unchunked.Ct1Sent) =>
      result = FunctionalModels.intoPb self ⦄ := by
  unfold into_pb FunctionalModels.intoPb
  step*
  simp_all [alloc.vec.Vec.deref, alloc.vec.Vec.eq_iff, alloc.vec.Vec.val, Slice.eq_iff]

end spqr.v1.unchunked.send_ct.serialize.Ct1Sent
