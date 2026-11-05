/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
module

public import SrcTranslated.Types
public import Spqr.Auxiliary.Aeneas.VecOfList

/-!
# Functional models of `spqr::encoding::polynomial::Poly::{serialize, deserialize}`

Pure, total Lean functions stating what the two Rust byte codecs compute, written against the
translated data types only, together with the well-formedness predicate and the round-trip laws
relating them. A `Poly` is a polynomial over GF(2¹⁶) stored as its coefficient vector, each
coefficient a 16-bit value. `serialize` writes every coefficient as two bytes, high byte first,
and `deserialize` reads the bytes back two at a time, rejecting the empty and the odd-length byte
strings. The underlying codec on coefficient lists, `bytesOfCoeffs` and `coeffsOfBytes`, is
shared with the functional models of `PolyEncoder`, whose `Points` state serialises the stored
points in exactly the same way. The spec theorems `serialize_spec` and `deserialize_spec` in
`Serialize.lean` and `Deserialize.lean` pin the extracted functions to these models.

The round-trip laws are three separate theorems:

• `roundtrip_deserialize_serialize` (RT1): every well-formed polynomial survives serialisation
  followed by deserialisation unchanged.

• `wellFormed_of_deserialize` (RT2a): every byte string the decoder accepts yields a well-formed
  polynomial.

• `roundtrip_serialize_deserialize` (RT2b): every byte string the decoder accepts is the
  serialisation of the polynomial it decodes to.

RT1, RT2a and RT2b together imply that:

• `serialize` and `deserialize` restrict to mutually inverse bijections between

  (i) the well-formed polynomials for `serialize`, and

  (ii) the byte strings that `deserialize` accepts.

• `WellFormed` characterises exactly the set of polynomials that survive serialisation followed
  by deserialisation unchanged.

**Source**: spqr/src/encoding/polynomial.rs
-/

@[expose] public section

open Aeneas.Std spqr.encoding.gf
namespace spqr.encoding.polynomial.Poly.FunctionalModels

/-- **Big-endian bytes of a field element**
• The two bytes of the 16-bit value `v` of a field element, high byte first:
  `[v / 256, v % 256]`. -/
def bytesOfGF16 (g : GF16) : List U8 :=
  [U8.ofNatCore (g.value.val / 256) ((Nat.div_lt_iff_lt_mul (by decide)).mpr g.value.hBounds),
   U8.ofNatCore (g.value.val % 256) (Nat.mod_lt _ (by decide))]

/-- **Field element of two big-endian bytes**
• The field element with the 16-bit value `256 * hi + lo`. -/
def gf16OfBytes (hi lo : U8) : GF16 :=
  { value := U16.ofNatCore (256 * hi.val + lo.val) (by
      have h1 : hi.val < 256 := hi.hBounds
      have h2 : lo.val < 256 := lo.hBounds
      change _ < 65536
      omega) }

/-- **Byte string of a coefficient list**
• Two big-endian bytes per coefficient, in coefficient order. -/
def bytesOfCoeffs (l : List GF16) : List U8 := l.flatMap bytesOfGF16

/-- **Coefficient list of a byte string**
• One coefficient per byte pair, in byte order; a trailing unpaired byte is dropped. -/
def coeffsOfBytes (b : List U8) : List GF16 :=
  match b with
  | hi :: lo :: rest => gf16OfBytes hi lo :: coeffsOfBytes rest
  | [_] => []
  | [] => []

/-- **Functional model of `spqr::encoding::polynomial::Poly::serialize`**
• A pure, total, human-readable function on the translated data types.
• The byte string `bytesOfCoeffs` of the coefficient list, as a vector. -/
def serialize (p : Poly) : alloc.vec.Vec U8 :=
  alloc.vec.Vec.ofList (bytesOfCoeffs p.coefficients.val)

/-- **Functional model of `spqr::encoding::polynomial::Poly::deserialize`**
• A pure, total, human-readable function on the translated data types.
• The coefficient list `coeffsOfBytes` of a non-empty byte string of even length, as a vector; an
  empty or odd-length byte string is `PolynomialError.SerializationInvalid`. -/
def deserialize (serialized : Slice U8) : core.result.Result Poly PolynomialError :=
  if serialized.val ≠ [] ∧ serialized.val.length % 2 = 0 then
    .Ok { coefficients := alloc.vec.Vec.ofList (coeffsOfBytes serialized.val) }
  else .Err PolynomialError.SerializationInvalid

/-- **Well-formedness predicate for `spqr::encoding::polynomial::Poly`**
• The polynomials that survive a round trip: at least one coefficient, since `deserialize`
  rejects the empty byte string, and few enough coefficients for the byte string to fit into a
  vector.
• The refine `coefficients.len() <= MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1 + 1` on the Rust struct
  is not checked by `deserialize`, so it is not part of the round-trip characterisation and is
  deliberately not transcribed. -/
def WellFormed (p : Poly) : Prop :=
  p.coefficients.val ≠ [] ∧ 2 * p.coefficients.length ≤ Usize.max

/-! ## Codec theorems

The helper facts about the list-level codec `bytesOfCoeffs` and `coeffsOfBytes` that everything
downstream rests on: the round-trip laws below, the spec theorems `serialize_spec` and
`deserialize_spec`, and the functional models and spec theorems of `PolyEncoder`, which reuse
the same codec for the stored points. -/

/-- The encoding of a coefficient list is twice as long. -/
@[simp] theorem bytesOfCoeffs_length (l : List GF16) : (bytesOfCoeffs l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    change (bytesOfGF16 g ++ bytesOfCoeffs l).length = _
    simp only [List.length_append, bytesOfGF16, List.length_cons, List.length_nil, ih]
    omega

/-- Decoding yields one coefficient per byte pair. -/
theorem coeffsOfBytes_length (b : List U8) : (coeffsOfBytes b).length = b.length / 2 :=
  match b with
  | [] => rfl
  | [_] => by simp only [coeffsOfBytes, List.length_nil, List.length_singleton, Nat.reduceDiv]
  | _ :: _ :: rest => by
    simp only [coeffsOfBytes, List.length_cons, coeffsOfBytes_length rest]
    exact (Nat.add_div_right _ Nat.two_pos).symm

/-- The encoding of a coefficient list is non-empty exactly when the list is. -/
theorem bytesOfCoeffs_ne_nil (l : List GF16) : bytesOfCoeffs l ≠ [] ↔ l ≠ [] := by
  rw [ne_eq, ne_eq, ← List.length_eq_zero_iff, ← List.length_eq_zero_iff, bytesOfCoeffs_length]
  omega

/-- The decoding of a byte string is non-empty exactly when the string holds a complete byte
pair. -/
theorem coeffsOfBytes_ne_nil (b : List U8) : coeffsOfBytes b ≠ [] ↔ 2 ≤ b.length := by
  rw [ne_eq, ← List.length_eq_zero_iff, coeffsOfBytes_length]
  omega

/-- `coeffsOfBytes` is a left inverse of `bytesOfCoeffs`. -/
theorem coeffsOfBytes_bytesOfCoeffs (l : List GF16) : coeffsOfBytes (bytesOfCoeffs l) = l := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    change coeffsOfBytes (bytesOfGF16 g ++ bytesOfCoeffs l) = g :: l
    rw [bytesOfGF16, List.cons_append, List.singleton_append, coeffsOfBytes, ih]
    congr 1
    apply congrArg GF16.mk
    apply UScalar.eq_of_val_eq
    simp only [U16.ofNatCore_val_eq, U8.ofNatCore_val_eq]
    exact Nat.div_add_mod _ _

/-- `bytesOfCoeffs` is a left inverse of `coeffsOfBytes` on even-length byte strings. -/
theorem bytesOfCoeffs_coeffsOfBytes (b : List U8) (h : b.length % 2 = 0) :
    bytesOfCoeffs (coeffsOfBytes b) = b :=
  match b, h with
  | [], _ => rfl
  | [_], h => nomatch h
  | hi :: lo :: rest, h => by
    change bytesOfGF16 (gf16OfBytes hi lo) ++ bytesOfCoeffs (coeffsOfBytes rest) = hi :: lo :: rest
    rw [bytesOfCoeffs_coeffsOfBytes rest
      (by simpa only [List.length_cons, Nat.add_assoc, Nat.reduceAdd, Nat.add_mod_right] using h)]
    have hlo : lo.val < 256 := lo.hBounds
    simp only [bytesOfGF16, gf16OfBytes, U16.ofNatCore_val_eq, List.cons_append, List.nil_append,
      List.cons.injEq, and_true]
    constructor <;> apply UScalar.eq_of_val_eq <;> simp only [U8.ofNatCore_val_eq] <;> omega

/-- A byte string is the encoding of a coefficient list exactly when it has twice the length and
holds every coefficient as a big-endian byte pair. -/
theorem eq_bytesOfCoeffs_iff (b : List U8) (l : List GF16) :
    b = bytesOfCoeffs l ↔ b.length = 2 * l.length ∧
      ∀ (k : Nat) (hk : k < l.length),
        256 * (b[2 * k]!).val + (b[2 * k + 1]!).val = (l[k]).value.val := by
  induction l generalizing b with
  | nil =>
    simp only [bytesOfCoeffs, List.flatMap_nil, List.length_nil, Nat.mul_zero,
      List.length_eq_zero_iff, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true, and_true]
  | cons g l ih =>
    match b with
    | [] | [_] =>
      refine iff_of_false (by
        simp only [bytesOfCoeffs, List.flatMap_cons, bytesOfGF16, List.cons_append,
          List.nil_append, List.nil_eq, List.cons.injEq, reduceCtorEq, and_false,
          not_false_eq_true]) fun ⟨h, _⟩ => ?_
      simp only [List.length_cons, List.length_nil] at h
      omega
    | hi :: lo :: rest =>
      change hi :: lo :: rest = bytesOfGF16 g ++ bytesOfCoeffs l ↔ _
      simp only [bytesOfGF16, List.cons_append, List.nil_append, List.cons.injEq, ih,
        List.length_cons]
      constructor
      · rintro ⟨rfl, rfl, hlen, hk⟩
        refine ⟨by omega, fun k hk' => ?_⟩
        rcases k with _ | k
        · simp only [Nat.mul_zero, List.getElem!_cons_zero, List.getElem!_cons_succ,
            U8.ofNatCore_val_eq, List.getElem_cons_zero]
          omega
        · simpa only [Nat.mul_add_one, List.getElem!_cons_succ, List.getElem_cons_succ] using
            hk k (by omega)
      · rintro ⟨hlen, hk⟩
        have hlo : lo.val < 256 := lo.hBounds
        have h0 := hk 0 (by omega)
        simp only [Nat.mul_zero, List.getElem!_cons_zero, List.getElem!_cons_succ,
          List.getElem_cons_zero] at h0
        refine ⟨?_, ?_, by omega, fun k hk' => by
          simpa only [Nat.mul_add_one, List.getElem!_cons_succ, List.getElem_cons_succ] using
            hk (k + 1) (Nat.add_lt_add_right hk' 1)⟩
        all_goals (apply UScalar.eq_of_val_eq; simp only [U8.ofNatCore_val_eq]; omega)

/-- Vector form of `eq_bytesOfCoeffs_iff`, provided the encoding fits into a vector. -/
theorem eq_ofList_bytesOfCoeffs_iff (v : alloc.vec.Vec U8) (l : List GF16)
    (hb : 2 * l.length ≤ Usize.max) :
    v = alloc.vec.Vec.ofList (bytesOfCoeffs l) ↔
      v.length = 2 * l.length ∧
        ∀ (k : Nat) (hk : k < l.length),
          256 * (v[2 * k]!).val + (v[2 * k + 1]!).val = (l[k]).value.val := by
  have hval : (alloc.vec.Vec.ofList (bytesOfCoeffs l)).val = bytesOfCoeffs l :=
    alloc.vec.Vec.ofList_val _ ((bytesOfCoeffs_length l).trans_le hb)
  simp only [alloc.vec.Vec.length, alloc.vec.Vec.getElem!_Nat_eq]
  rw [← eq_bytesOfCoeffs_iff]
  exact ⟨fun h => by rw [h, hval], fun h => alloc.vec.Vec.ext _ _ (h.trans hval.symm)⟩

/-! ## Round-trip laws -/

/-- **Round trip `deserialize ∘ serialize` (RT1) for `spqr::encoding::polynomial::Poly`**
• Every well-formed polynomial survives serialisation followed by deserialisation unchanged. -/
@[simp]
theorem roundtrip_deserialize_serialize (p : Poly) (h : WellFormed p) :
    deserialize (alloc.vec.Vec.deref (serialize p)) = .Ok p := by
  obtain ⟨hne, hb⟩ := h
  have hval : (serialize p).val = bytesOfCoeffs p.coefficients.val :=
    alloc.vec.Vec.ofList_val _ ((bytesOfCoeffs_length _).trans_le hb)
  have hacc : (alloc.vec.Vec.deref (serialize p)).val ≠ [] ∧
      (alloc.vec.Vec.deref (serialize p)).val.length % 2 = 0 := by
    simp only [alloc.vec.Vec.deref, Slice.from_val, hval, bytesOfCoeffs_length]
    exact ⟨(bytesOfCoeffs_ne_nil _).mpr hne, by omega⟩
  unfold deserialize
  rw [ite_eq_left hacc]
  simp only [alloc.vec.Vec.deref, Slice.from_val, hval, coeffsOfBytes_bytesOfCoeffs,
    alloc.vec.Vec.val_ofList]

/-- **Accepted byte strings yield well-formed polynomials (RT2a) for
`spqr::encoding::polynomial::Poly`**
• Every polynomial the decoder successfully produces satisfies `WellFormed`. -/
theorem wellFormed_of_deserialize (serialized : Slice U8) (p : Poly)
    (h : deserialize serialized = .Ok p) : WellFormed p := by
  unfold deserialize at h
  split_ifs at h with hacc
  · simp only [core.result.Result.Ok.injEq] at h
    subst h
    obtain ⟨hne, hev⟩ := hacc
    have hval : (alloc.vec.Vec.ofList (coeffsOfBytes serialized.val)).val =
        coeffsOfBytes serialized.val :=
      alloc.vec.Vec.ofList_val _
        (by rw [coeffsOfBytes_length]; exact (Nat.div_le_self _ _).trans serialized.property)
    simp only [WellFormed, alloc.vec.Vec.length, hval]
    exact ⟨(coeffsOfBytes_ne_nil _).mpr (by have := List.length_pos_of_ne_nil hne; omega),
      by rw [coeffsOfBytes_length]; exact (Nat.mul_div_le _ _).trans serialized.property⟩

/-- **Round trip `serialize ∘ deserialize` (RT2b) for `spqr::encoding::polynomial::Poly`**
• Every accepted byte string is the serialisation of the polynomial it decodes to. -/
theorem roundtrip_serialize_deserialize (serialized : Slice U8) (p : Poly)
    (h : deserialize serialized = .Ok p) : alloc.vec.Vec.deref (serialize p) = serialized := by
  unfold deserialize at h
  split_ifs at h with hacc
  · simp only [core.result.Result.Ok.injEq] at h
    subst h
    obtain ⟨-, hev⟩ := hacc
    apply Slice.ext
    simp only [alloc.vec.Vec.deref, Slice.from_val, serialize,
      alloc.vec.Vec.ofList_val (coeffsOfBytes serialized.val)
        (by rw [coeffsOfBytes_length]; exact (Nat.div_le_self _ _).trans serialized.property),
      bytesOfCoeffs_coeffsOfBytes _ hev, alloc.vec.Vec.ofList_val _ serialized.property]

end spqr.encoding.polynomial.Poly.FunctionalModels
