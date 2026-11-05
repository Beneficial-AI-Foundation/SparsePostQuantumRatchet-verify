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
functions to these models. A `PolyEncoder` holds the chunk counter `idx` and either 16 stored
points (`Points`) or 16 polynomials (`Polys`). `into_pb` copies `idx` and fills exactly one of
the protobuf byte lists `pts` and `polys`, encoding every entry with
`Poly.FunctionalModels.serialize`. `from_pb` decodes whichever list is filled with
`Poly.FunctionalModels.coeffsOfBytes` and rejects every other shape.

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
• Copies `idx`. A `Points` state fills `pts` with `Poly.FunctionalModels.serialize` of every
  stored point, and leaves `polys` empty; a `Polys` state fills `polys` with
  `Poly.FunctionalModels.serialize` of every polynomial and leaves `pts` empty. -/
def intoPb : PolyEncoder → PolynomialEncoder
  | ⟨idx, .Points points⟩ =>
    { idx,
      pts := .ofList (points.val.map fun p => Poly.FunctionalModels.serialize ⟨p.value⟩),
      polys := .new _ }
  | ⟨idx, .Polys polys⟩ =>
    { idx, pts := .new _, polys := .ofList (polys.val.map Poly.FunctionalModels.serialize) }

/-- **Functional model of `spqr::encoding::polynomial::PolyEncoder::from_pb`**
• A pure, total, human-readable function on the translated data types.
• Copies `idx`. If `pts` is empty and `polys` holds 16 non-empty byte strings of even length,
  the state is `Polys` of their `Poly.FunctionalModels.coeffsOfBytes` as polynomials; if instead
  `polys` is empty and `pts` holds 16 byte strings of even length, the state is `Points` of their
  `Poly.FunctionalModels.coeffsOfBytes` as points.
  Every other shape is `PolynomialError.SerializationInvalid`. -/
def fromPb : PolynomialEncoder → core.result.Result PolyEncoder PolynomialError
  | ⟨idx, pts, polys⟩ =>
    let decode (v : alloc.vec.Vec U8) :=
      alloc.vec.Vec.ofList (Poly.FunctionalModels.coeffsOfBytes v.val)
    if h : pts.val = [] ∧ polys.length = 16 ∧ ∀ v ∈ polys.val, v.val ≠ [] ∧ v.length % 2 = 0 then
      .Ok { idx, s := .Polys (.from (polys.val.map (Poly.mk ∘ decode)) (by simp [h.2.1])) }
    else if h : polys.val = [] ∧ pts.length = 16 ∧ ∀ v ∈ pts.val, v.length % 2 = 0 then
      .Ok { idx, s := .Points (.from (pts.val.map (Point.mk ∘ decode)) (by simp [h.2.1])) }
    else .Err .SerializationInvalid

/-- **Well-formedness predicate for `spqr::encoding::polynomial::PolyEncoder`**
• The in-memory states that survive a round trip: in a `Points` state every stored point must be
  short enough for its byte string to fit into a vector, and in a `Polys` state every polynomial
  must be well-formed as a `Poly`, i.e. non-empty and short enough as well.
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
  · have hbyte : ∀ p ∈ points.val,
        (Poly.FunctionalModels.serialize { coefficients := p.value }).val =
          Poly.FunctionalModels.bytesOfCoeffs p.value.val := fun p hp =>
      alloc.vec.Vec.ofList_val _ ((Poly.FunctionalModels.bytesOfCoeffs_length _).trans_le (h p hp))
    have hpts := alloc.vec.Vec.ofList_val
      (points.val.map fun p => Poly.FunctionalModels.serialize { coefficients := p.value })
      (by rw [List.length_map, points.property]
          exact (UScalar.hrBounds _).trans_eq ((UScalar.rMax_eq_max _).trans UScalar.max_USize_eq))
    have heven : ∀ v ∈ points.val.map (fun p =>
        Poly.FunctionalModels.serialize { coefficients := p.value }), v.length % 2 = 0 :=
      List.forall_mem_map.mpr fun p hp => by
        rw [alloc.vec.Vec.length, hbyte p hp, Poly.FunctionalModels.bytesOfCoeffs_length]
        exact Nat.mul_mod_right 2 _
    unfold fromPb intoPb
    dsimp only
    rw [dite_eq_right, dite_eq_left]
    case hnc => exact fun h1 => absurd h1.2.1 (by decide)
    case hc => exact ⟨rfl, by simp [hpts], by rw [hpts]; exact heven⟩
    simp only [core.result.Result.Ok.injEq, PolyEncoder.mk.injEq, EncoderState.Points.injEq,
      true_and]
    apply Aeneas.Std.Array.ext
    rw [Array.from_val, hpts, List.map_map]
    refine (List.map_congr_left fun p hp => ?_).trans (List.map_id' _)
    simp only [Function.comp_def, hbyte p hp, Poly.FunctionalModels.coeffsOfBytes_bytesOfCoeffs,
      alloc.vec.Vec.val_ofList]
  · have hbyte : ∀ p ∈ polys.val, (Poly.FunctionalModels.serialize p).val =
        Poly.FunctionalModels.bytesOfCoeffs p.coefficients.val := fun p hp =>
      alloc.vec.Vec.ofList_val _
        ((Poly.FunctionalModels.bytesOfCoeffs_length _).trans_le (h p hp).2)
    have hpolys := alloc.vec.Vec.ofList_val (polys.val.map Poly.FunctionalModels.serialize)
      (by rw [List.length_map, polys.property]
          exact (UScalar.hrBounds _).trans_eq ((UScalar.rMax_eq_max _).trans UScalar.max_USize_eq))
    have hacc : ∀ v ∈ polys.val.map Poly.FunctionalModels.serialize,
        v.val ≠ [] ∧ v.length % 2 = 0 :=
      List.forall_mem_map.mpr fun p hp => by
        rw [alloc.vec.Vec.length, hbyte p hp, Poly.FunctionalModels.bytesOfCoeffs_length]
        exact ⟨(Poly.FunctionalModels.bytesOfCoeffs_ne_nil _).mpr (h p hp).1,
          Nat.mul_mod_right 2 _⟩
    unfold fromPb intoPb
    dsimp only
    rw [dite_eq_left]
    case hc => exact ⟨rfl, by simp [hpolys], by rw [hpolys]; exact hacc⟩
    simp only [core.result.Result.Ok.injEq, PolyEncoder.mk.injEq, EncoderState.Polys.injEq,
      true_and]
    apply Aeneas.Std.Array.ext
    rw [Array.from_val, hpolys, List.map_map]
    refine (List.map_congr_left fun p hp => ?_).trans (List.map_id' _)
    simp only [Function.comp_def, hbyte p hp,
      Poly.FunctionalModels.coeffsOfBytes_bytesOfCoeffs, alloc.vec.Vec.val_ofList]

/-- **Successfully decoded protobuf input states yield well-formed in-memory states (RT2a) for
`spqr::encoding::polynomial::PolyEncoder`**
• Every in-memory state the decoder successfully produces satisfies `WellFormed`. -/
theorem wellFormed_of_fromPb (pb : PolynomialEncoder) (x : PolyEncoder)
    (h : fromPb pb = .Ok x) : WellFormed x := by
  unfold fromPb at h
  dsimp only at h
  split at h
  next h1 =>
    obtain rfl := core.result.Result.Ok.inj h
    simp only [WellFormed, Array.from_val, List.forall_mem_map, Function.comp_def]
    intro v hv
    obtain ⟨hne, hev⟩ := h1.2.2 v hv
    simp only [alloc.vec.Vec.length] at hev
    simp only [Poly.FunctionalModels.WellFormed, alloc.vec.Vec.length,
      alloc.vec.Vec.ofList_val (Poly.FunctionalModels.coeffsOfBytes v.val)
        (by rw [Poly.FunctionalModels.coeffsOfBytes_length]
            exact (Nat.div_le_self _ _).trans v.property)]
    exact ⟨(Poly.FunctionalModels.coeffsOfBytes_ne_nil _).mpr
        (Nat.le_of_dvd (List.length_pos_of_ne_nil hne) (Nat.dvd_of_mod_eq_zero hev)),
      by rw [Poly.FunctionalModels.coeffsOfBytes_length]
         exact (Nat.mul_div_le _ _).trans v.property⟩
  · split at h
    · obtain rfl := core.result.Result.Ok.inj h
      simp only [WellFormed, Array.from_val, List.forall_mem_map, Function.comp_def]
      intro v hv
      simp only [alloc.vec.Vec.length,
        alloc.vec.Vec.ofList_val (Poly.FunctionalModels.coeffsOfBytes v.val)
          (by rw [Poly.FunctionalModels.coeffsOfBytes_length]
              exact (Nat.div_le_self _ _).trans v.property),
        Poly.FunctionalModels.coeffsOfBytes_length]
      exact (Nat.mul_div_le _ _).trans v.property
    · nomatch h

/-- **Round trip `intoPb ∘ fromPb` (RT2b) for
`spqr::encoding::polynomial::PolyEncoder`**
• Every successfully decoded protobuf state is the encoding of the in-memory state it
  decodes to. -/
theorem roundtrip_intoPb_fromPb (pb : PolynomialEncoder) (x : PolyEncoder)
    (h : fromPb pb = .Ok x) : intoPb x = pb := by
  rcases pb with ⟨idx, pts, polys⟩
  unfold fromPb at h
  dsimp only at h
  split at h
  next h1 =>
    obtain rfl := core.result.Result.Ok.inj h
    obtain ⟨hpts, -, hacc⟩ := h1
    simp only [intoPb, Array.from_val, List.map_map, PolynomialEncoder.mk.injEq, true_and]
    refine ⟨alloc.vec.Vec.ext _ _ hpts.symm, (congrArg alloc.vec.Vec.ofList
      ((List.map_congr_left fun v hv => ?_).trans (List.map_id' _))).trans
      (alloc.vec.Vec.val_ofList _)⟩
    obtain ⟨-, hev⟩ := hacc v hv
    simp only [Function.comp_def, Poly.FunctionalModels.serialize,
      alloc.vec.Vec.ofList_val (Poly.FunctionalModels.coeffsOfBytes v.val)
        (by rw [Poly.FunctionalModels.coeffsOfBytes_length]
            exact (Nat.div_le_self _ _).trans v.property),
      Poly.FunctionalModels.bytesOfCoeffs_coeffsOfBytes _ hev, alloc.vec.Vec.val_ofList]
  · split at h
    next h2 =>
      obtain rfl := core.result.Result.Ok.inj h
      obtain ⟨hpolys, -, hev⟩ := h2
      simp only [intoPb, Array.from_val, List.map_map, PolynomialEncoder.mk.injEq, true_and]
      refine ⟨(congrArg alloc.vec.Vec.ofList
        ((List.map_congr_left fun v hv => ?_).trans (List.map_id' _))).trans
        (alloc.vec.Vec.val_ofList _), alloc.vec.Vec.ext _ _ hpolys.symm⟩
      simp only [Function.comp_def, Poly.FunctionalModels.serialize,
        alloc.vec.Vec.ofList_val (Poly.FunctionalModels.coeffsOfBytes v.val)
          (by rw [Poly.FunctionalModels.coeffsOfBytes_length]
              exact (Nat.div_le_self _ _).trans v.property),
        Poly.FunctionalModels.bytesOfCoeffs_coeffsOfBytes _ (hev v hv), alloc.vec.Vec.val_ofList]
    · nomatch h

end spqr.encoding.polynomial.PolyEncoder.FunctionalModels
