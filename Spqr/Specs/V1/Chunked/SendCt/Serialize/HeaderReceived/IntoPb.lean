/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
module

public import SrcTranslated.Funs
import Spqr.Specs.V1.Unchunked.SendCt.Serialize.HeaderReceived.IntoPb
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.IntoPb
public import Spqr.Specs.V1.Chunked.SendCt.Serialize.HeaderReceived.FunctionalModels

/-!
# Spec theorem for `spqr::v1::chunked::send_ct::serialize::HeaderReceived::into_pb`

Converts a chunked `HeaderReceived` state from its in-memory Rust form
(`spqr::v1::chunked::send_ct::HeaderReceived`) into the protobuf form
(`spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived`) used for saving it to disk. The
chunked state has two fields, each converted separately and wrapped in `Some` since the
corresponding protobuf fields are optional: the unchunked part `uc` with the unchunked
`HeaderReceived::into_pb` and the decoder `receiving_ek` with `PolyDecoder::into_pb`, whose overflow
hypothesis this spec inherits. The result is pinned to the pure functional model
`FunctionalModels.intoPb`, which in turn calls the functional models of the component
conversions. The reverse direction is `from_pb`.

**Source**: spqr/src/v1/chunked/send_ct/serialize.rs
-/

@[expose] public section

open Aeneas Aeneas.Std Result
namespace spqr.v1.chunked.send_ct.serialize.HeaderReceived

/-- **Spec theorem for `spqr::v1::chunked::send_ct::serialize::HeaderReceived::into_pb`**
• The call always succeeds (no panic) under the overflow hypothesis inherited from
  `PolyDecoder::into_pb` for `self.receiving_ek`: `4 * len ≤ Usize.max` on the number `len` of
  points in every slot.
• The extracted function agrees with its associated high-level functional model
  `FunctionalModels.intoPb` (see def).
-/
@[step]
theorem into_pb_spec (self : v1.chunked.send_ct.HeaderReceived)
    (h_overflow : ∀ s ∈ self.receiving_ek.pts.val, 4 * s.length ≤ Usize.max) :
    into_pb self ⦃ (result : proto.pq_ratchet.v1_state.chunked.HeaderReceived) =>
      result = FunctionalModels.intoPb self ⦄ := by
  unfold into_pb FunctionalModels.intoPb
  refine WP.spec_bind (unchunked.send_ct.serialize.HeaderReceived.into_pb_spec self.uc) ?_
  rintro _ rfl
  refine WP.spec_bind
    (encoding.polynomial.PolyDecoder.into_pb_spec self.receiving_ek h_overflow) ?_
  rintro _ rfl
  exact (WP.spec_ok _).mpr rfl

end spqr.v1.chunked.send_ct.serialize.HeaderReceived
