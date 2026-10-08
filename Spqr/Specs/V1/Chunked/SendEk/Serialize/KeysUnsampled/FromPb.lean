/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Unchunked.SendEk.Serialize.KeysUnsampled.FromPb
import Spqr.Specs.V1.Chunked.SendEk.Serialize.KeysUnsampled.FunctionalModels

/-!
# Spec theorem for `spqr::v1::chunked::send_ek::serialize::KeysUnsampled::from_pb`

Converts a chunked `KeysUnsampled` state from the protobuf form
(`spqr::proto::pq_ratchet::v1_state::chunked::KeysUnsampled`), as read back from disk, into
the in-memory Rust form (`spqr::v1::chunked::send_ek::KeysUnsampled`). The chunked state just
wraps a single unchunked field `uc`, but the corresponding protobuf field is optional, so it
must be present (`Error::StateDecode` otherwise). The conversion then delegates to the
unchunked `KeysUnsampled::from_pb` and propagates its error, if any. The result is pinned to
the pure functional model `FunctionalModels.fromPb`, which in turn calls the functional model
of the unchunked conversion. The reverse direction is `into_pb`.

**Source**: spqr/src/v1/chunked/send_ek/serialize.rs
-/

open Aeneas Aeneas.Std Result
namespace spqr.v1.chunked.send_ek.serialize.KeysUnsampled

/-- **Spec theorem for `spqr::v1::chunked::send_ek::serialize::KeysUnsampled::from_pb`**
• The call always succeeds (no panic).
• The extracted function agrees with its associated high-level functional model
  `FunctionalModels.fromPb` (see def).
-/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.v1_state.chunked.KeysUnsampled) :
    from_pb pb ⦃ (result : core.result.Result v1.chunked.send_ek.KeysUnsampled Error) =>
      result = FunctionalModels.fromPb pb ⦄ := by
  unfold from_pb FunctionalModels.fromPb
  rcases pb with ⟨_ | ⟨_, _ | _⟩⟩ <;> step* <;>
    simp_all [unchunked.send_ek.serialize.KeysUnsampled.FunctionalModels.fromPb]

end spqr.v1.chunked.send_ek.serialize.KeysUnsampled
