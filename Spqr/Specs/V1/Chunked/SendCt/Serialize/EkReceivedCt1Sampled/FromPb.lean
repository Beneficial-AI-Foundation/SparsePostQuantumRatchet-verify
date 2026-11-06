/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
module

public import SrcTranslated.Funs
import Spqr.Specs.V1.Unchunked.SendCt.Serialize.Ct1SentEkReceived.FromPb
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.FromPb
public import Spqr.Specs.V1.Chunked.SendCt.Serialize.EkReceivedCt1Sampled.FunctionalModels

/-!
# Spec theorem for `spqr::v1::chunked::send_ct::serialize::EkReceivedCt1Sampled::from_pb`

Converts a chunked `EkReceivedCt1Sampled` state from the protobuf form
(`spqr::proto::pq_ratchet::v1_state::chunked::EkReceivedCt1Sampled`), as read back from disk, into
the in-memory Rust form (`spqr::v1::chunked::send_ct::EkReceivedCt1Sampled`). The chunked state has
two fields, `uc` and `sending_ct1`, and the corresponding protobuf fields are both optional, so each
must be present (`Error::StateDecode` otherwise). The unchunked part `uc` is converted with the
unchunked `Ct1SentEkReceived::from_pb`, whose error is propagated, and the encoder `sending_ct1`
with `PolyEncoder::from_pb`, whose `PolynomialError` is mapped to `Error::StateDecode`. The result
is pinned to the pure functional model `FunctionalModels.fromPb`, which in turn calls the functional
models of the component conversions. The reverse direction is `into_pb`.

**Source**: spqr/src/v1/chunked/send_ct/serialize.rs
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial
namespace spqr.v1.chunked.send_ct.serialize.EkReceivedCt1Sampled

/-- **Spec theorem for `spqr::v1::chunked::send_ct::serialize::EkReceivedCt1Sampled::from_pb`**
• The call always succeeds (no panic).
• The extracted function agrees with its associated high-level functional model
  `FunctionalModels.fromPb` (see def).
-/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.v1_state.chunked.EkReceivedCt1Sampled) :
    from_pb pb ⦃ (result : core.result.Result v1.chunked.send_ct.EkReceivedCt1Sampled Error) =>
      result = FunctionalModels.fromPb pb ⦄ := by
  unfold from_pb FunctionalModels.fromPb
  have h_err (u : proto.pq_ratchet.v1_state.unchunked.Ct1SentEkReceived) (e : Error)
      (h : unchunked.send_ct.serialize.Ct1SentEkReceived.FunctionalModels.fromPb u = .Err e) :
      e = Error.StateDecode := by
    unfold unchunked.send_ct.serialize.Ct1SentEkReceived.FunctionalModels.fromPb at h
    split at h <;> cases h
    rfl
  rcases pb with ⟨_ | u, _ | p⟩ <;>
    simp only [core.option.Option.ok_or, bind_ok, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, Option.map_none, Option.map_some, WP.spec_ok]
  all_goals
    refine WP.spec_bind (unchunked.send_ct.serialize.Ct1SentEkReceived.from_pb_spec u) ?_
    rintro _ rfl
    rcases hu : unchunked.send_ct.serialize.Ct1SentEkReceived.FunctionalModels.fromPb u with uc | e
  case some.none.Ok => simp only [bind_ok, WP.spec_ok]
  case some.none.Err => obtain rfl := h_err u e hu; simp only [bind_ok, WP.spec_ok]
  case some.some.Err => obtain rfl := h_err u e hu; simp only [bind_ok, WP.spec_ok]
  case some.some.Ok =>
    simp only [bind_ok]
    refine WP.spec_bind (PolyEncoder.from_pb_spec p) ?_
    rintro _ rfl
    rcases PolyEncoder.FunctionalModels.fromPb p with s | e <;>
      simp only [bind_ok, core.result.Result.map_err,
        from_pb.closure.Insts.CoreOpsFunctionFnOnceTuplePolynomialErrorError.call_once,
        WP.spec_ok]

end spqr.v1.chunked.send_ct.serialize.EkReceivedCt1Sampled
