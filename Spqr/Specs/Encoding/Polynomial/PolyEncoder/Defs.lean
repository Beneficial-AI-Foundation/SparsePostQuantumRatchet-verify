/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong, Markus Dablander
-/
import SrcTranslated.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Gf2Poly.Basic
import Spqr.Math.Poly.Identities.Basic

/-! # Postcondition predicates for `PolyEncoder`

The named postconditions that the `PolyEncoder` spec theorems are stated against, together with
some pure lemmas relating them.

-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf spqr.math.gf

namespace spqr.encoding.polynomial.PolyEncoder

/-- Default `Inhabited` instance for `Point` (empty value vector), needed for the `[j]!`
lookups in `IntoPbPostCond`. -/
instance instInhabitedPoint : Inhabited encoding.polynomial.Point :=
  ⟨⟨alloc.vec.Vec.new _⟩⟩

/-- **Postcondition predicate for `PolyEncoder.into_pb`**

The postcondition of `into_pb_spec`: the byte-level serialization identities together
with the derived GF(2¹⁶) and binary-polynomial identities. -/
def IntoPbPostCond (self : PolyEncoder)
    (result : proto.pq_ratchet.PolynomialEncoder) : Prop :=
  result.idx = self.idx ∧
  match self.s with
  | .Points points =>
    result.polys.val = [] ∧
    result.pts.length = points.length ∧
    ∀ j < points.length,
        result.pts[j]!.length = 2 * (points[j]!).value.length ∧
        ∀ k < (points[j]!).value.length,
            256 * (result.pts[j]!)[2 * k]! + (result.pts[j]!)[2 * k + 1]! =
              ((points[j]!).value[k]!).value.val ∧
            (256 * (result.pts[j]!)[2 * k]! + (result.pts[j]!)[2 * k + 1]! : ℕ).toGF216 =
              ((points[j]!).value[k]!).value.val.toGF216 ∧
            natToBinaryPoly (256 * (result.pts[j]!)[2 * k]! + (result.pts[j]!)[2 * k + 1]!) =
              natToBinaryPoly (((points[j]!).value[k]!).value.val)
  | .Polys polys =>
    result.pts.val = [] ∧
    result.polys.length = polys.length ∧
    ∀ j < polys.length,
        (result.polys[j]!).length =
          2 * (polys[j]!).degree ∧
        ∀ k < (polys[j]!).degree,
             256 * (result.polys[j]!)[2 * k]! + (result.polys[j]!)[2 * k + 1]! =
              ((polys[j]!).coefficients[k]! ).value.val ∧
            (256 * (result.polys[j]!)[2 * k]! + (result.polys[j]!)[2 * k + 1]! : ℕ).toGF216 =
              ((polys[j]!).coefficients[k]!).value.val.toGF216 ∧
            natToBinaryPoly (
              256 * (result.polys[j]!)[2 * k]! + (result.polys[j]!)[2 * k + 1]! ) =
              natToBinaryPoly (((polys[j]!).coefficients[k]!).value.val)

/-- The two shapes `from_pb` accepts without outputting an error result. -/
def FromPbWellFormed (pb : proto.pq_ratchet.PolynomialEncoder) : Prop :=
  (pb.pts.val = [] ∧ pb.polys.length = 16 ∧
      ∀ j < 16, (pb.polys[j]!).length ≠ 0 ∧ (pb.polys[j]!).length % 2 = 0) ∨
  (pb.polys.val = [] ∧ pb.pts.length = 16 ∧
      ∀ j < 16, (pb.pts[j]!).length % 2 = 0)

instance instDecidableFromPbWellFormed (pb : proto.pq_ratchet.PolynomialEncoder) :
    Decidable (FromPbWellFormed pb) := by
  unfold FromPbWellFormed
  infer_instance

/-- Postcondition of `from_pb_spec`. Reusage of `IntoPbPostCond` pins `from_pb` down as the
inverse of `into_pb`; this avoids restating the entire byte layout. -/
def FromPbPostCond (pb : proto.pq_ratchet.PolynomialEncoder)
    (result : core.result.Result PolyEncoder PolynomialError) : Prop :=
  if FromPbWellFormed pb then
    match result with
    | core.result.Result.Ok encoder => IntoPbPostCond encoder pb
    | core.result.Result.Err _ => False
  else result = core.result.Result.Err PolynomialError.SerializationInvalid

/- The rest of the file exists to establish that the recent refactor lost nothing: the new spec
   generalises the old one, while allowing to drop all three input hypotheses and to pin
   down the error case. -/

/-- The exact postcondition fromt the old `from_pb_spec` before it was generalised,
with the byte-level, GF(2¹⁶) and binary polynomial identities spelled out behind implications.
Stays silent about rejected inputs. -/
def FromPbPostCondOldPartial (pb : proto.pq_ratchet.PolynomialEncoder)
    (result : core.result.Result PolyEncoder PolynomialError) : Prop :=
  (pb.pts.val = [] → pb.polys.val.length = 16 →
    match result with
    | core.result.Result.Ok encoder =>
        encoder.idx = pb.idx ∧
        match encoder.s with
        | EncoderState.Polys out =>
            ∀ j < 16, (out[j]!).degree = (pb.polys[j]!).length / 2 ∧
                ∀ k < (pb.polys[j]!).length / 2,
                    (out[j]!.coefficients[k]!).value.val =
                      256 * ((pb.polys[j]!)[2 * k]!).val + ((pb.polys[j]!)[2 * k + 1]!).val ∧
                    ((out[j]!.coefficients[k]!).value.val).toGF216 =
                      (256 * ((pb.polys[j]!)[2 * k]!).val +
                       ((pb.polys[j]!)[2 * k + 1]!).val).toGF216 ∧
                    natToBinaryPoly (out[j]!.coefficients[k]!).value.val =
                      natToBinaryPoly
                        (256 * ((pb.polys[j]!)[2 * k]!).val +
                         ((pb.polys[j]!)[2 * k + 1]!).val)
        | _ => False
    | core.result.Result.Err _ => False) ∧
  (pb.polys.val = [] → pb.pts.length = 16 →
    match result with
    | core.result.Result.Ok encoder =>
        encoder.idx = pb.idx ∧
        match encoder.s with
        | EncoderState.Points out =>
            ∀ j < 16, (out[j]!).value.length = (pb.pts[j]!).length / 2 ∧
            ∀ k < (pb.pts[j]!).length / 2,
                ((out[j]!).value[k]!).value.val =
                256 * ((pb.pts[j]!)[2 * k]!).val + ((pb.pts[j]!)[2 * k + 1]!).val ∧
                (((out[j]!).value[k]!).value.val).toGF216 =
                  (256 * ((pb.pts[j]!)[2 * k]!).val + ((pb.pts[j]!)[2 * k + 1]!).val).toGF216 ∧
                natToBinaryPoly ((out[j]!).value[k]!).value.val =
                natToBinaryPoly (256 * ((pb.pts[j]!)[2 * k]!).val +
                         ((pb.pts[j]!)[2 * k + 1]!).val)
        | _ => False
    | core.result.Result.Err _ => False)

/-- A lemma that derives `FromPbPostCondOldPartial` from the new `FromPbPostCond`, given the
three hypotheses on `pb` that the old spec assumed. -/
lemma from_pb_new_implies_old_partial
    (pb : proto.pq_ratchet.PolynomialEncoder)
    (h_polys_nonempty : pb.pts.val = [] → ∀ j < pb.polys.length, (pb.polys[j]!).length ≠ 0)
    (h_polys_even : pb.pts.val = [] → ∀ j < pb.polys.length, (pb.polys[j]!).length % 2 = 0)
    (h_pts_even : pb.polys.val = [] → ∀ j < pb.pts.length, (pb.pts[j]!).length % 2 = 0)
    (result : core.result.Result PolyEncoder PolynomialError)
    (h_total : FromPbPostCond pb result) :
    FromPbPostCondOldPartial pb result := by
  unfold FromPbPostCond at h_total
  unfold FromPbPostCondOldPartial
  refine ⟨fun h_nil h_len => ?_, fun h_nil h_len => ?_⟩
  · have h_len' : pb.polys.length = 16 := h_len
    rw [if_pos (show FromPbWellFormed pb from .inl ⟨h_nil, h_len', fun j hj =>
      ⟨h_polys_nonempty h_nil j (by omega), h_polys_even h_nil j (by omega)⟩⟩)] at h_total
    match result, h_total with
    | .Ok ⟨_, .Points _⟩, ⟨_, h_polys_nil, _⟩ => simp [h_polys_nil] at h_len
    | .Ok ⟨_, .Polys out⟩, ⟨h_idx, _, _, h_body⟩ =>
      have h_out : out.length = 16 := out.property
      refine ⟨h_idx.symm, fun j hj => ?_⟩
      obtain ⟨h_lenj, h_co⟩ := h_body j (by omega)
      refine ⟨by omega, fun k hk => ?_⟩
      obtain ⟨e1, e2, e3⟩ := h_co k (by omega)
      exact ⟨e1.symm, e2.symm, e3.symm⟩
  · rw [if_pos (show FromPbWellFormed pb from .inr ⟨h_nil, h_len, fun j hj =>
      h_pts_even h_nil j (by omega)⟩)] at h_total
    match result, h_total with
    | .Ok ⟨_, .Polys _⟩, ⟨_, h_pts_nil, _⟩ => simp [h_pts_nil] at h_len
    | .Ok ⟨_, .Points out⟩, ⟨h_idx, _, _, h_body⟩ =>
      have h_out : out.length = 16 := out.property
      refine ⟨h_idx.symm, fun j hj => ?_⟩
      obtain ⟨h_lenj, h_co⟩ := h_body j (by omega)
      refine ⟨by omega, fun k hk => ?_⟩
      obtain ⟨e1, e2, e3⟩ := h_co k (by omega)
      exact ⟨e1.symm, e2.symm, e3.symm⟩

end spqr.encoding.polynomial.PolyEncoder
