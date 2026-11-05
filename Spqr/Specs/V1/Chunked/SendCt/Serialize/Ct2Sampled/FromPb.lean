/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
module

public import SrcTranslated.Funs
import Spqr.Specs.V1.Unchunked.SendCt.Serialize.Ct2Sent.FromPb
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.FromPb
public import Spqr.Specs.V1.Chunked.SendCt.Serialize.Ct2Sampled.FunctionalModels

/-!
# Spec theorem for `spqr::v1::chunked::send_ct::serialize::Ct2Sampled::from_pb`

Converts a chunked `Ct2Sampled` state from the protobuf form
(`spqr::proto::pq_ratchet::v1_state::chunked::Ct2Sampled`), as read back from disk, into the
in-memory Rust form (`spqr::v1::chunked::send_ct::Ct2Sampled`). The chunked state has two
fields, `uc` and `sending_ct2`, and the corresponding protobuf fields are both optional, so each
must be present (`Error::StateDecode` otherwise). The unchunked part `uc` is converted with the
unchunked `Ct2Sent::from_pb`, whose error is propagated, and the encoder `sending_ct2` with
`PolyEncoder::from_pb`, whose `PolynomialError` is mapped to `Error::StateDecode`. The result is
pinned to the pure functional model `FunctionalModels.fromPb`, which in turn calls the functional
models of the component conversions. The reverse direction is `into_pb`.

**Source**: spqr/src/v1/chunked/send_ct/serialize.rs
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial
namespace spqr.v1.chunked.send_ct.serialize.Ct2Sampled

/-- **Spec theorem for `spqr::v1::chunked::send_ct::serialize::Ct2Sampled::from_pb`**
• The call always succeeds (no panic).
• The extracted function agrees with its associated high-level functional model
  `FunctionalModels.fromPb` (see def).
-/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.v1_state.chunked.Ct2Sampled) :
    from_pb pb ⦃ (result : core.result.Result v1.chunked.send_ct.Ct2Sampled Error) =>
      result = FunctionalModels.fromPb pb ⦄ := by
  unfold from_pb FunctionalModels.fromPb
  have h_map_err (r : core.result.Result PolyEncoder PolynomialError) :
      core.result.Result.map_err
        from_pb.closure.Insts.CoreOpsFunctionFnOnceTuplePolynomialErrorError r () ⦃ res =>
        res = match r with | .Ok v => .Ok v | .Err _ => .Err Error.StateDecode ⦄ := by
    cases r <;> simp [from_pb.closure.Insts.CoreOpsFunctionFnOnceTuplePolynomialErrorError,
      from_pb.closure.Insts.CoreOpsFunctionFnOnceTuplePolynomialErrorError.call_once]
  rcases pb with ⟨_ | u, _ | p⟩ <;> step* <;>
    grind [unchunked.send_ct.serialize.Ct2Sent.FunctionalModels.fromPb]

end spqr.v1.chunked.send_ct.serialize.Ct2Sampled
