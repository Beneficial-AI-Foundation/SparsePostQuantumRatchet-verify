/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
module

import SrcTranslated.Funs
import Spqr.Specs.V1.Unchunked.SendCt.Serialize.Ct1Sent.FromPb
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.FromPb
import Spqr.Specs.IncrementalMlkem768.ENCAPSULATION_KEY_SIZE
public import Spqr.Specs.V1.Chunked.SendCt.Serialize.Ct1Acknowledged.FunctionalModels

/-!
# Spec theorem for `spqr::v1::chunked::send_ct::serialize::Ct1Acknowledged::from_pb`

Converts a chunked `Ct1Acknowledged` state from the protobuf form
(`spqr::proto::pq_ratchet::v1_state::chunked::Ct1Acknowledged`), as read back from disk, into the
in-memory Rust form (`spqr::v1::chunked::send_ct::Ct1Acknowledged`). It first checks the fact that
a present decoder `receiving_ek` needs `576` points, the value of `ENCAPSULATION_KEY_SIZE / 2`
(`Error::MsgDecode` otherwise). The chunked state has two fields, `uc` and `receiving_ek`, and the
corresponding protobuf fields are both optional, so each must be present (`Error::StateDecode`
otherwise). The unchunked part `uc` is converted with the unchunked `Ct1Sent::from_pb`, whose error
is propagated, and the decoder `receiving_ek` with `PolyDecoder::from_pb`, whose `PolynomialError`
is mapped to `Error::StateDecode`. The result is pinned to the pure functional model
`FunctionalModels.fromPb`, which in turn calls the functional models of the component conversions.
The reverse direction is `into_pb`.

**Source**: spqr/src/v1/chunked/send_ct/serialize.rs
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial
namespace spqr.v1.chunked.send_ct.serialize.Ct1Acknowledged

/-- **Spec theorem for `spqr::v1::chunked::send_ct::serialize::Ct1Acknowledged::from_pb`**
• The call always succeeds (no panic).
• The extracted function agrees with its associated high-level functional model
  `FunctionalModels.fromPb` (see def).
-/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.v1_state.chunked.Ct1Acknowledged) :
    from_pb pb ⦃ (result : core.result.Result v1.chunked.send_ct.Ct1Acknowledged Error) =>
      result = FunctionalModels.fromPb pb ⦄ := by
  have h_err (u : proto.pq_ratchet.v1_state.unchunked.Ct1Sent) (e : Error)
      (h : unchunked.send_ct.serialize.Ct1Sent.FunctionalModels.fromPb u = .Err e) :
      e = Error.StateDecode := by
    unfold unchunked.send_ct.serialize.Ct1Sent.FunctionalModels.fromPb at h
    split at h <;> cases h
    rfl
  rcases pb with ⟨uc?, ek?⟩
  rewrite [FunctionalModels.fromPb]
  refine WP.spec_bind (Pₘ := fun ob =>
    (ob = (ek?, true) ∧ ∃ d ∈ ek?, d.pts_needed.val ≠ 576) ∨
      ob = (ek?, false) ∧ ¬∃ d ∈ ek?, d.pts_needed.val ≠ 576) ?_ ?_
  · rcases ek? with _ | d
    · exact (WP.spec_ok _).mpr (.inr ⟨rfl, fun h => h.elim fun _ h => Option.not_mem_none _ h.1⟩)
    have hcast := U32.cast_Usize_val_eq d.pts_needed
    obtain ⟨i2, hi2, (hi2v : i2.val = 576)⟩ :=
      UScalar.div_spec 1152#usize (y := 2#usize) (by decide)
    change WP.spec (Std.bind _ _) _
    rewrite [lift, bind_ok, incremental_mlkem768.ENCAPSULATION_KEY_SIZE_eq, bind_ok, hi2,
      bind_ok]
    rcases hb : UScalar.cast .Usize d.pts_needed != i2 with _ | _
    · have hn : d.pts_needed.val = 576 :=
        hcast.symm.trans ((congrArg UScalar.val (bne_eq_false_iff_eq.mp hb)).trans hi2v)
      rewrite [ite_eq_right Bool.false_ne_true, bind_ok]
      exact (WP.spec_ok _).mpr
        (.inr ⟨rfl, fun h => h.elim fun _ h => h.2 (Option.some.inj h.1 ▸ hn)⟩)
    · rewrite [ite_eq_left rfl, bind_ok]
      exact (WP.spec_ok _).mpr (.inl ⟨rfl, d, rfl, fun hn =>
        bne_iff_ne.mp hb (UScalar.eq_of_val_eq (hcast.trans (hn.trans hi2v.symm)))⟩)
  rintro _ (⟨rfl, hg⟩ | ⟨rfl, hg⟩)
  · rewrite [uncurry_apply_pair, ite_eq_left rfl, ite_eq_left hg]
    exact (WP.spec_ok _).mpr rfl
  rewrite [uncurry_apply_pair, ite_eq_right Bool.false_ne_true, ite_eq_right hg]
  rcases uc? with _ | u
  · rewrite [core.option.Option.ok_or.eq_2, bind_ok,
      core.result.Result.Insts.CoreOpsTry.branch.eq_2, bind_ok]
    exact core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual_Err.spec
      _ _ _ _ rfl
  rewrite [core.option.Option.ok_or.eq_1, bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch.eq_1, bind_ok, Option.map_some]
  refine WP.spec_bind (unchunked.send_ct.serialize.Ct1Sent.from_pb_spec u) ?_
  rintro _ rfl
  rcases hu : unchunked.send_ct.serialize.Ct1Sent.FunctionalModels.fromPb u with uc | e
  swap
  · obtain rfl := h_err u e hu
    rewrite [core.result.Result.Insts.CoreOpsTry.branch.eq_2, bind_ok]
    exact core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual_Err.spec
      _ _ _ _ rfl
  rewrite [core.result.Result.Insts.CoreOpsTry.branch.eq_1, bind_ok]
  change WP.spec (Std.bind _ _) _
  rcases ek? with _ | d
  · rewrite [core.option.Option.ok_or.eq_2, bind_ok,
      core.result.Result.Insts.CoreOpsTry.branch.eq_2, bind_ok]
    exact core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual_Err.spec
      _ _ _ _ rfl
  rewrite [core.option.Option.ok_or.eq_1, bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch.eq_1, bind_ok, Option.map_some]
  refine WP.spec_bind (PolyDecoder.from_pb_spec d) ?_
  rintro _ rfl
  rcases PolyDecoder.FunctionalModels.fromPb d with s | e
  · rewrite [core.result.Result.map_err_Ok, bind_ok,
      core.result.Result.Insts.CoreOpsTry.branch.eq_1, bind_ok]
    exact (WP.spec_ok _).mpr rfl
  rewrite [core.result.Result.map_err_Err]
  dsimp only [from_pb.closure.Insts.CoreOpsFunctionFnOnceTuplePolynomialErrorError.call_once]
  rewrite [bind_ok, bind_ok, core.result.Result.Insts.CoreOpsTry.branch.eq_2, bind_ok]
  exact core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual_Err.spec
    _ _ _ _ rfl

end spqr.v1.chunked.send_ct.serialize.Ct1Acknowledged
