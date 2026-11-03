/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
module

public import SrcTranslated.Types
public import Spqr.Specs.Encoding.Polynomial.Poly.FunctionalModels

/-!
# Functional models of `spqr::encoding::polynomial::PolyEncoder::{into_pb, from_pb}`

Pure, total Lean functions stating what the two Rust serializers compute, written against the
translated data types only, together with the well-formedness predicate and the round-trip laws
relating them. The spec theorems in `IntoPb.lean` and `FromPb.lean` pin the extracted, monadic
functions to these models. A `PolyEncoder` holds the chunk counter `idx` and one of two states:
`Points`, 16 lists of stored field elements, or `Polys`, 16 polynomials. `into_pb` copies `idx`
and fills exactly one of the two protobuf byte lists, `pts` from a `Points` state and `polys`
from a `Polys` state, writing every field element as two bytes, high byte first; `from_pb`
rebuilds the state from whichever list is filled and rejects every other shape. The nested
components are handled with the `Poly` functional models: `into_pb` writes each polynomial via
`Poly.FunctionalModels.serialize`, and otherwise polynomials and stored points alike go through
the coefficient codec `Poly.FunctionalModels.bytesOfCoeffs` and
`Poly.FunctionalModels.coeffsOfBytes`, which the Rust code inlines for points.

The round-trip laws are three separate theorems:

• `roundtrip_fromPb_intoPb` (RT1): every well-formed in-memory state survives encoding followed by
  decoding unchanged.

• `wellFormed_of_fromPb` (RT2a): every protobuf state the decoder successfully decodes yields a
  well-formed in-memory state.

• `roundtrip_intoPb_fromPb` (RT2b): every protobuf state the decoder successfully decodes is the
  encoding of the associated in-memory state it decodes to.

RT1, RT2a and RT2b together imply that:

• `intoPb` and `fromPb` restrict to mutually inverse bijections between

  (i) the well-formed in-memory input states for `intoPb`, and

  (ii) the protobuf input states that `fromPb` successfully decodes.

• `WellFormed` characterises exactly the set of in-memory input states for `intoPb` that survive
  encoding followed by decoding unchanged.

**Source**: spqr/src/encoding/polynomial.rs
-/

@[expose] public section

open Aeneas.Std spqr.proto.pq_ratchet
namespace spqr.encoding.polynomial.PolyEncoder.FunctionalModels

/-- **Functional model of `spqr::encoding::polynomial::PolyEncoder::into_pb`**
• A pure, total, human-readable function on the translated data types.
• Copies `idx`. A `Points` state fills `pts` with the byte string
  `Poly.FunctionalModels.bytesOfCoeffs` of every stored point and leaves `polys` empty; a `Polys`
  state fills `polys` with `Poly.FunctionalModels.serialize` of every polynomial and leaves `pts`
  empty. -/
def intoPb (x : PolyEncoder) : PolynomialEncoder :=
  match x.s with
  | .Points points =>
    { idx := x.idx,
      pts := alloc.vec.Vec.from (points.val.map fun p =>
        alloc.vec.Vec.ofList (Poly.FunctionalModels.bytesOfCoeffs p.value.val)) (by scalar_tac),
      polys := alloc.vec.Vec.new _ }
  | .Polys polys =>
    { idx := x.idx,
      pts := alloc.vec.Vec.new _,
      polys := alloc.vec.Vec.from (polys.val.map Poly.FunctionalModels.serialize) (by scalar_tac) }

/-- **Functional model of `spqr::encoding::polynomial::PolyEncoder::from_pb`**
• A pure, total, human-readable function on the translated data types.
• Copies `idx`. If `pts` is empty and `polys` holds 16 non-empty byte strings of even length,
  the state is `Polys` of their `Poly.FunctionalModels.coeffsOfBytes` as polynomials; if instead
  `polys` is empty and `pts` holds 16 byte strings of even length, the state is `Points` of their
  `Poly.FunctionalModels.coeffsOfBytes` as points.
  Every other shape is `PolynomialError.SerializationInvalid`. -/
def fromPb (pb : PolynomialEncoder) : core.result.Result PolyEncoder PolynomialError :=
  if h : pb.pts.val = [] ∧ pb.polys.length = 16 ∧
      ∀ v ∈ pb.polys.val, v.val ≠ [] ∧ v.length % 2 = 0 then
    .Ok { idx := pb.idx,
          s := .Polys (Array.from
            (pb.polys.val.map fun v =>
              { coefficients := alloc.vec.Vec.ofList (Poly.FunctionalModels.coeffsOfBytes v.val) })
            (by simp [h.2.1])) }
  else if h : pb.polys.val = [] ∧ pb.pts.length = 16 ∧ ∀ v ∈ pb.pts.val, v.length % 2 = 0 then
    .Ok { idx := pb.idx,
          s := .Points (Array.from
            (pb.pts.val.map fun v =>
              { value := alloc.vec.Vec.ofList (Poly.FunctionalModels.coeffsOfBytes v.val) })
            (by simp [h.2.1])) }
  else .Err PolynomialError.SerializationInvalid

/-- **Well-formedness predicate for `spqr::encoding::polynomial::PolyEncoder`**
• The in-memory states that survive a round trip: in a `Points` state every stored point must be
  short enough for its byte string to fit into a vector, and in a `Polys` state every polynomial
  must be well-formed as a `Poly`, i.e. non-empty and short enough, since `from_pb` rejects the
  empty byte string.
• `PolyEncoder` itself carries no refine annotation. The refines on its components, `Point`
  (`value.len() <= MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1`) and `Poly`
  (`coefficients.len() <= MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1 + 1`), are not checked by
  `from_pb`, which only `hax_lib::assume!`s the former, so they are not part of the round-trip
  characterisation and are deliberately not transcribed. -/
def WellFormed (x : PolyEncoder) : Prop :=
  match x.s with
  | .Points points => ∀ p ∈ points.val, 2 * p.value.length ≤ Usize.max
  | .Polys polys => ∀ p ∈ polys.val, Poly.FunctionalModels.WellFormed p

/-- **Round trip `fromPb ∘ intoPb` (RT1) for
`spqr::encoding::polynomial::PolyEncoder`**
• Every well-formed in-memory state survives encoding followed by decoding unchanged. -/
@[simp]
theorem roundtrip_fromPb_intoPb (x : PolyEncoder) (h : WellFormed x) :
    fromPb (intoPb x) = .Ok x := by
  rcases x with ⟨idx, points | polys⟩
  · simp only [WellFormed] at h
    have hbyte : ∀ p ∈ points.val,
        (alloc.vec.Vec.ofList (Poly.FunctionalModels.bytesOfCoeffs p.value.val)).val =
          Poly.FunctionalModels.bytesOfCoeffs p.value.val := fun p hp =>
      alloc.vec.Vec.ofList_val _ ((Poly.FunctionalModels.bytesOfCoeffs_length _).trans_le (h p hp))
    have heven : ∀ v ∈ points.val.map (fun p =>
        alloc.vec.Vec.ofList (Poly.FunctionalModels.bytesOfCoeffs p.value.val)),
        v.length % 2 = 0 := by
      intro v hv
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
      simp only [alloc.vec.Vec.length, hbyte p hp, Poly.FunctionalModels.bytesOfCoeffs_length]
      exact Nat.mul_mod_right 2 _
    unfold fromPb intoPb
    simp only [alloc.vec.Vec.from_val]
    split_ifs with h1 h2
    · simp [alloc.vec.Vec.new] at h1
    · simp only [core.result.Result.Ok.injEq, PolyEncoder.mk.injEq, EncoderState.Points.injEq,
        true_and]
      apply Aeneas.Std.Array.ext
      rw [Array.from_val, List.map_map]
      refine (List.map_congr_left fun p hp => ?_).trans (List.map_id' _)
      simp only [Function.comp_def, hbyte p hp, Poly.FunctionalModels.coeffsOfBytes_bytesOfCoeffs,
        alloc.vec.Vec.val_ofList]
    · exact absurd ⟨by simp, by simp, heven⟩ h2
  · simp only [WellFormed] at h
    have hbyte : ∀ p ∈ polys.val, (Poly.FunctionalModels.serialize p).val =
        Poly.FunctionalModels.bytesOfCoeffs p.coefficients.val := fun p hp =>
      alloc.vec.Vec.ofList_val _
        ((Poly.FunctionalModels.bytesOfCoeffs_length _).trans_le (h p hp).2)
    have hacc : ∀ v ∈ polys.val.map Poly.FunctionalModels.serialize,
        v.val ≠ [] ∧ v.length % 2 = 0 := by
      intro v hv
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
      obtain ⟨hne, -⟩ := h p hp
      simp only [alloc.vec.Vec.length, hbyte p hp, Poly.FunctionalModels.bytesOfCoeffs_length]
      exact ⟨(Poly.FunctionalModels.bytesOfCoeffs_ne_nil _).mpr hne, Nat.mul_mod_right 2 _⟩
    unfold fromPb intoPb
    simp only [alloc.vec.Vec.from_val]
    split_ifs with h1
    · simp only [core.result.Result.Ok.injEq, PolyEncoder.mk.injEq, EncoderState.Polys.injEq,
        true_and]
      apply Aeneas.Std.Array.ext
      rw [Array.from_val, List.map_map]
      refine (List.map_congr_left fun p hp => ?_).trans (List.map_id' _)
      simp only [Function.comp_def, hbyte p hp,
        Poly.FunctionalModels.coeffsOfBytes_bytesOfCoeffs, alloc.vec.Vec.val_ofList]
    all_goals exact absurd ⟨by simp, by simp, hacc⟩ h1

/-- **Successfully decoded protobuf input states yield well-formed in-memory states (RT2a) for
`spqr::encoding::polynomial::PolyEncoder`**
• Every in-memory state the decoder successfully produces satisfies `WellFormed`. -/
theorem wellFormed_of_fromPb (pb : PolynomialEncoder) (x : PolyEncoder)
    (h : fromPb pb = .Ok x) : WellFormed x := by
  unfold fromPb at h
  split_ifs at h with h1 h2
  · simp only [core.result.Result.Ok.injEq] at h
    subst h
    simp only [WellFormed, Array.from_val, List.forall_mem_map]
    intro v hv
    obtain ⟨hne, hev⟩ := h1.2.2 v hv
    simp only [alloc.vec.Vec.length] at hev
    simp only [Poly.FunctionalModels.WellFormed, alloc.vec.Vec.length,
      alloc.vec.Vec.ofList_val (Poly.FunctionalModels.coeffsOfBytes v.val)
        (by rw [Poly.FunctionalModels.coeffsOfBytes_length]
            exact (Nat.div_le_self _ _).trans v.property)]
    exact ⟨(Poly.FunctionalModels.coeffsOfBytes_ne_nil _).mpr
        (by have := List.length_pos_of_ne_nil hne; omega),
      by rw [Poly.FunctionalModels.coeffsOfBytes_length]
         exact (Nat.mul_div_le _ _).trans v.property⟩
  · simp only [core.result.Result.Ok.injEq] at h
    subst h
    simp only [WellFormed, Array.from_val, List.forall_mem_map]
    intro v hv
    simp only [alloc.vec.Vec.length,
      alloc.vec.Vec.ofList_val (Poly.FunctionalModels.coeffsOfBytes v.val)
        (by rw [Poly.FunctionalModels.coeffsOfBytes_length]
            exact (Nat.div_le_self _ _).trans v.property),
      Poly.FunctionalModels.coeffsOfBytes_length]
    exact (Nat.mul_div_le _ _).trans v.property

/-- **Round trip `intoPb ∘ fromPb` (RT2b) for
`spqr::encoding::polynomial::PolyEncoder`**
• Every successfully decoded protobuf state is the encoding of the in-memory state it
  decodes to. -/
theorem roundtrip_intoPb_fromPb (pb : PolynomialEncoder) (x : PolyEncoder)
    (h : fromPb pb = .Ok x) : intoPb x = pb := by
  rcases pb with ⟨idx, pts, polys⟩
  unfold fromPb at h
  split_ifs at h with h1 h2
  · simp only [core.result.Result.Ok.injEq] at h
    subst h
    obtain ⟨hpts, -, hacc⟩ := h1
    simp only [intoPb, Array.from_val, List.map_map, PolynomialEncoder.mk.injEq, true_and]
    refine ⟨alloc.vec.Vec.ext _ _ (by simp [alloc.vec.Vec.new, hpts]), alloc.vec.Vec.ext _ _ ?_⟩
    rw [alloc.vec.Vec.from_val]
    refine (List.map_congr_left fun v hv => ?_).trans (List.map_id' _)
    obtain ⟨-, hev⟩ := hacc v hv
    simp only [Function.comp_def, Poly.FunctionalModels.serialize,
      alloc.vec.Vec.ofList_val (Poly.FunctionalModels.coeffsOfBytes v.val)
        (by rw [Poly.FunctionalModels.coeffsOfBytes_length]
            exact (Nat.div_le_self _ _).trans v.property),
      Poly.FunctionalModels.bytesOfCoeffs_coeffsOfBytes _ hev, alloc.vec.Vec.val_ofList]
  · simp only [core.result.Result.Ok.injEq] at h
    subst h
    obtain ⟨hpolys, -, hev⟩ := h2
    simp only [intoPb, Array.from_val, List.map_map, PolynomialEncoder.mk.injEq, true_and]
    refine ⟨alloc.vec.Vec.ext _ _ ?_, alloc.vec.Vec.ext _ _ (by simp [alloc.vec.Vec.new, hpolys])⟩
    rw [alloc.vec.Vec.from_val]
    refine (List.map_congr_left fun v hv => ?_).trans (List.map_id' _)
    simp only [Function.comp_def,
      alloc.vec.Vec.ofList_val (Poly.FunctionalModels.coeffsOfBytes v.val)
        (by rw [Poly.FunctionalModels.coeffsOfBytes_length]
            exact (Nat.div_le_self _ _).trans v.property),
      Poly.FunctionalModels.bytesOfCoeffs_coeffsOfBytes _ (hev v hv), alloc.vec.Vec.val_ofList]

end spqr.encoding.polynomial.PolyEncoder.FunctionalModels
