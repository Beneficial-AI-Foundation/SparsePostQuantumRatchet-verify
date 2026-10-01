/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Unchunked.SendEk.Serialize.KeysUnsampled.IntoPb
import Spqr.Specs.V1.Chunked.SendEk.Serialize.KeysUnsampled.FunctionalModels

/-!
# Spec theorem for `spqr::v1::chunked::send_ek::serialize::KeysUnsampled::into_pb`

Converts a chunked `KeysUnsampled` state from its in-memory Rust form
(`spqr::v1::chunked::send_ek::KeysUnsampled`) into the protobuf form
(`spqr::proto::pq_ratchet::v1_state::chunked::KeysUnsampled`) used for saving it to disk.
The chunked state just wraps a single unchunked field `uc`, so the conversion delegates to
the unchunked `KeysUnsampled::into_pb` and wraps its result in `Some`, since the protobuf
field is optional. The result is pinned to the pure functional model `FunctionalModels.intoPb`,
which in turn calls the functional model of the unchunked conversion. The reverse direction is
`from_pb`.

**Source:** "src/v1/chunked/send_ek/serialize.rs"
-/

open Aeneas Aeneas.Std Result
namespace spqr.v1.chunked.send_ek.serialize.KeysUnsampled

/-- **Spec theorem for `spqr::v1::chunked::send_ek::serialize::KeysUnsampled::into_pb`**
• The call always succeeds (no panic).
• The extracted function agrees with its associated high-level functional model
  `FunctionalModels.intoPb` (see def).
-/
@[step]
theorem into_pb_spec (self : v1.chunked.send_ek.KeysUnsampled) :
    into_pb self ⦃ (result : proto.pq_ratchet.v1_state.chunked.KeysUnsampled) =>
      result = FunctionalModels.intoPb self ⦄ := by
  unfold into_pb FunctionalModels.intoPb
  step*

end spqr.v1.chunked.send_ek.serialize.KeysUnsampled
