/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
module

public import SrcTranslated.Funs
import Spqr.Specs.V1.Unchunked.SendEk.Serialize.EkSentCt1Received.FromPb
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.FromPb
public import Spqr.Specs.V1.Chunked.SendEk.Serialize.Ct1Received.FunctionalModels

/-!
# Spec theorem for `spqr::v1::chunked::send_ek::serialize::Ct1Received::from_pb`

Converts a chunked `Ct1Received` state from the protobuf form
(`spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received`), as read back from disk, into the
in-memory Rust form (`spqr::v1::chunked::send_ek::Ct1Received`). The chunked state has two
fields, `uc` and `sending_ek`, and the corresponding protobuf fields are both optional, so each
must be present (`Error::StateDecode` otherwise). The unchunked part `uc` is converted with the
unchunked `EkSentCt1Received::from_pb`, whose error is propagated, and the encoder `sending_ek` with
`PolyEncoder::from_pb`, whose `PolynomialError` is mapped to `Error::StateDecode`. The result is
pinned to the pure functional model `FunctionalModels.fromPb`, which in turn calls the functional
models of the component conversions. The reverse direction is `into_pb`.

**Source**: spqr/src/v1/chunked/send_ek/serialize.rs
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial
namespace spqr.v1.chunked.send_ek.serialize.Ct1Received

/-- **Spec theorem for `spqr::v1::chunked::send_ek::serialize::Ct1Received::from_pb`**
• The call always succeeds (no panic).
• The extracted function agrees with its associated high-level functional model
  `FunctionalModels.fromPb` (see def).
-/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.v1_state.chunked.Ct1Received) :
    from_pb pb ⦃ (result : core.result.Result v1.chunked.send_ek.Ct1Received Error) =>
      result = FunctionalModels.fromPb pb ⦄ := by
  unfold from_pb FunctionalModels.fromPb
  have h_err (u : proto.pq_ratchet.v1_state.unchunked.EkSentCt1Received) (e : Error)
      (h : unchunked.send_ek.serialize.EkSentCt1Received.FunctionalModels.fromPb u = .Err e) :
      e = Error.StateDecode := by
    unfold unchunked.send_ek.serialize.EkSentCt1Received.FunctionalModels.fromPb at h
    split at h <;> cases h
    rfl
  rcases pb with ⟨_ | u, ek?⟩
  · rw [core.option.Option.ok_or.eq_2, bind_ok, core.result.Result.Insts.CoreOpsTry.branch.eq_2,
      bind_ok]
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual.eq_2,
      core.convert.FromSame.from, bind_tc_ok, Option.map_none, WP.spec_ok]
  · rw [core.option.Option.ok_or.eq_1, bind_ok, core.result.Result.Insts.CoreOpsTry.branch.eq_1,
      bind_ok, Option.map_some]
    refine WP.spec_bind (unchunked.send_ek.serialize.EkSentCt1Received.from_pb_spec u) ?_
    rintro _ rfl
    rcases hu : unchunked.send_ek.serialize.EkSentCt1Received.FunctionalModels.fromPb u with uc | e
    · rw [core.result.Result.Insts.CoreOpsTry.branch.eq_1, bind_ok]
      dsimp only
      rcases ek? with _ | p
      · rw [core.option.Option.ok_or.eq_2, bind_ok,
          core.result.Result.Insts.CoreOpsTry.branch.eq_2, bind_ok]
        simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual.eq_2,
          core.convert.FromSame.from, bind_tc_ok, Option.map_none, WP.spec_ok]
      · rw [core.option.Option.ok_or.eq_1, bind_ok,
          core.result.Result.Insts.CoreOpsTry.branch.eq_1, bind_ok, Option.map_some]
        refine WP.spec_bind (PolyEncoder.from_pb_spec p) ?_
        rintro _ rfl
        rcases PolyEncoder.FunctionalModels.fromPb p with s | e
        · simp only [core.result.Result.map_err.eq_1, bind_ok,
            core.result.Result.Insts.CoreOpsTry.branch.eq_1, WP.spec_ok]
        · simp only [core.result.Result.map_err.eq_2,
            from_pb.closure.Insts.CoreOpsFunctionFnOnceTuplePolynomialErrorError.call_once, bind_ok,
            core.result.Result.Insts.CoreOpsTry.branch.eq_2,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual.eq_2,
            core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    · obtain rfl := h_err u e hu
      rw [core.result.Result.Insts.CoreOpsTry.branch.eq_2, bind_ok]
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual.eq_2,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]

end spqr.v1.chunked.send_ek.serialize.Ct1Received
