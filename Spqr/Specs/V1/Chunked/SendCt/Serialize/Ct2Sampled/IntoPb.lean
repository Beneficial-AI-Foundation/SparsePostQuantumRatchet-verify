/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
module

public import SrcTranslated.Funs
import Spqr.Specs.V1.Unchunked.SendCt.Serialize.Ct2Sent.IntoPb
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.IntoPb
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.Defs
public import Spqr.Specs.V1.Chunked.SendCt.Serialize.Ct2Sampled.FunctionalModels

/-!
# Spec theorem for `spqr::v1::chunked::send_ct::serialize::Ct2Sampled::into_pb`

Converts a chunked `Ct2Sampled` state from its in-memory Rust form
(`spqr::v1::chunked::send_ct::Ct2Sampled`) into the protobuf form
(`spqr::proto::pq_ratchet::v1_state::chunked::Ct2Sampled`) used for saving it to disk. The
chunked state has two fields, each converted separately and wrapped in `Some` since the
corresponding protobuf fields are optional: the unchunked part `uc` with the unchunked
`Ct2Sent::into_pb` and the encoder `sending_ct2` with `PolyEncoder::into_pb`, whose two overflow
hypotheses this spec inherits. The result is pinned to the pure functional model
`FunctionalModels.intoPb`, which in turn calls the functional models of the component
conversions. The reverse direction is `from_pb`.

**Source**: spqr/src/v1/chunked/send_ct/serialize.rs
-/

@[expose] public section

open Aeneas Aeneas.Std Result
namespace spqr.v1.chunked.send_ct.serialize.Ct2Sampled

/-- **Spec theorem for `spqr::v1::chunked::send_ct::serialize::Ct2Sampled::into_pb`**
• The call always succeeds (no panic) under the two overflow hypotheses inherited from
  `PolyEncoder::into_pb` for `self.sending_ct2`: `2 * len ≤ Usize.max` on the coefficient count
  `len` of every stored point and polynomial.
• The extracted function agrees with its associated high-level functional model
  `FunctionalModels.intoPb` (see def).
-/
@[step]
theorem into_pb_spec (self : v1.chunked.send_ct.Ct2Sampled)
    (h_overflow_points : ∀ points, self.sending_ct2.s = .Points points →
      ∀ j < points.length, 2 * points[j]!.value.length ≤ Usize.max)
    (h_overflow_polys : ∀ polys, self.sending_ct2.s = .Polys polys →
      ∀ j < polys.length, 2 * polys[j]!.degree ≤ Usize.max) :
    into_pb self ⦃ (result : proto.pq_ratchet.v1_state.chunked.Ct2Sampled) =>
      result = FunctionalModels.intoPb self ⦄ := by
  unfold into_pb FunctionalModels.intoPb
  step*

end spqr.v1.chunked.send_ct.serialize.Ct2Sampled
