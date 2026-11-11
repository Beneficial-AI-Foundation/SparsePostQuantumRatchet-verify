/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
module

public import SrcTranslated.Types
public import Spqr.Specs.Encoding.Polynomial.Poly.FunctionalModels
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.PointsValid

/-!
# Functional models of `spqr::encoding::polynomial::PolyDecoder::{into_pb, from_pb}`

Pure, total Lean functions stating what the two Rust serializers compute, written against the
translated data types only, together with the well-formedness predicate and the round-trip laws
relating them. The spec theorems in `IntoPb.lean` and `FromPb.lean` pin the extracted, monadic
functions to these models.

A `PolyDecoder` collects received points `(x, y)` in 16 slots. Once enough points are in, it can
reconstruct the message they carry. `into_pb` encodes a `PolyDecoder` (the in-memory state) as a
`PolynomialDecoder` (the protobuf state), a plain record of numbers and byte strings that can be
stored, and `from_pb` decodes it back. Both states have these three fields:

• `pts_needed`: how many points, counted over all 16 slots, are needed to reconstruct the
  message. The protobuf state holds it as a 32-bit number, so values of `2 ^ 32` or more do not
  survive encoding.

• `pts`: the 16 slots. In the in-memory state, each slot keeps its points ordered by `x`, smallest
  first, and never holds two points with the same `x`. In the protobuf state, each slot is a byte
  string that lists its points in that order, four bytes per point.

• `is_complete`: a true/false flag; while it is true, the `PolyDecoder` outputs no message.

The protobuf state has one more field, `polys`, which encoding always sets to `16`.

Decoding accepts more than encoding produces. It ignores `polys`, and it accepts slots whose
points are out of order or repeat an `x`: it starts from an empty slot and adds the points one at
a time, each at its place in the order, and a point whose `x` is already there replaces the old
one. For example, the byte strings for `[(5, a), (2, b)]` and for `[(2, c), (5, a), (2, b)]` both
decode to the slot `[(2, b), (5, a)]`, and encoding that slot gives a third byte string, the one
for `[(2, b), (5, a)]`. So several protobuf states decode to the same in-memory state, and exactly
one of them is what encoding it produces. `Canonical` picks out that one: `polys` is `16`, there
are 16 byte strings, the length of each is divisible by four, and the points of each are ordered
by `x` without repeats.

The round-trip laws are four separate theorems. The RT1 laws start from an in-memory state and the
RT2 laws from a protobuf state. Each `a` law says where one model sends its inputs, and each `b`
law describes a round trip.

• `canonical_intoPb` (RT1a): every well-formed in-memory state encodes to a canonical protobuf
  state.

• `roundtrip_fromPb_intoPb` (RT1b): every well-formed in-memory state survives encoding followed by
  decoding unchanged.

• `wellFormed_of_fromPb` (RT2a): every protobuf state the decoder successfully decodes yields a
  well-formed in-memory state.

• `roundtrip_intoPb_fromPb` (RT2b): every canonical protobuf state survives decoding followed by
  encoding unchanged.

Together, RT1a and RT2a say that `intoPb` sends well-formed in-memory states to canonical protobuf
states and that `fromPb` sends every protobuf state it decodes to a well-formed in-memory state.
RT1b and RT2b say that `fromPb ∘ intoPb` is the identity on the well-formed in-memory states and
that `intoPb ∘ fromPb` is the identity on the canonical protobuf states.

**So `intoPb` and `fromPb` restrict to mutually inverse bijections between
the well-formed in-memory states and the canonical protobuf states.**

Moreover, `WellFormed` and `Canonical` characterise exactly the states that survive their
respective round trips: every in-memory state that survives is well-formed by RT2a, and every
protobuf state that survives is canonical by RT2a and RT1a.

**Source**: spqr/src/encoding/polynomial.rs
-/

@[expose] public section

open Aeneas.Std spqr.proto.pq_ratchet spqr.encoding.polynomial.Poly.FunctionalModels
namespace spqr.encoding.polynomial.PolyDecoder.FunctionalModels

/-- **Byte string of a point list**
• Four bytes per point, in list order: the two big-endian bytes of `x`, then those of `y`. -/
def bytesOfPts (l : List Pt) : List U8 := l.flatMap fun p => bytesOfGF16 p.x ++ bytesOfGF16 p.y

/-- **Point list of a byte string**
• One point per four bytes `b0 b1 b2 b3`, in byte order, with abscissa `256 * b0 + b1` and
  ordinate `256 * b2 + b3`; one to three trailing bytes are dropped. -/
def ptsOfBytes : List U8 → List Pt
  | b0 :: b1 :: b2 :: b3 :: rest =>
    { x := gf16OfBytes b0 b1, y := gf16OfBytes b2 b3 } :: ptsOfBytes rest
  | _ => []

/-- **Functional model of `sorted_vec::SortedSet<Pt>::push` on a sorted slot**
• The points of `l` with abscissa below that of `p`, then `p`, then the points of `l` with
  abscissa above it: `p` replaces the point with its abscissa, if any. `push` computes this on
  sorted slots only (`push_spec_insertPt` in `FromPb.lean`). -/
def insertPt (l : List Pt) (p : Pt) : List Pt :=
  l.filter (·.x.value.val < p.x.value.val) ++ p :: l.filter (p.x.value.val < ·.x.value.val)

/-- **Byte vector of a slot**
• The byte string `bytesOfPts` of the points of the slot, as a vector. -/
def bytesOfSlot (s : sorted_vec.SortedSet Pt) : alloc.vec.Vec U8 :=
  .ofList (bytesOfPts s.val)

/-- **Slot decoded from a byte vector**
• The points `ptsOfBytes` of the byte vector, pushed one after another into the empty slot. -/
def slotOfBytes (v : alloc.vec.Vec U8) : sorted_vec.SortedSet Pt :=
  .ofList ((ptsOfBytes v.val).foldl insertPt [])

/-- **Functional model of `spqr::encoding::polynomial::PolyDecoder::into_pb`**
• A pure, total, human-readable function on the translated data types.
• Casts `pts_needed` to `u32`, writes `16` into `polys`, copies `is_complete` and encodes every
  slot with `bytesOfSlot`. -/
def intoPb : PolyDecoder → PolynomialDecoder
  | ⟨pts_needed, pts, is_complete⟩ =>
    { pts_needed := pts_needed.cast .U32,
      polys := 16#u32,
      pts := .ofList (pts.val.map bytesOfSlot),
      is_complete := is_complete }

/-- **Functional model of `spqr::encoding::polynomial::PolyDecoder::from_pb`**
• A pure, total, human-readable function on the translated data types.
• Fails with `PolynomialError.SerializationInvalid` unless `pts` holds exactly 16 byte strings,
  each of a length divisible by four.
• Otherwise decodes the `i`-th byte string into the `i`-th slot with `slotOfBytes`, casts
  `pts_needed` to `usize` and copies `is_complete`. The field `polys` is never read. -/
def fromPb : PolynomialDecoder → core.result.Result PolyDecoder PolynomialError
  | ⟨pts_needed, _, pts, is_complete⟩ =>
    if h : pts.length = 16 ∧ ∀ v ∈ pts.val, v.length % 4 = 0 then
      .Ok { pts_needed := pts_needed.cast .Usize,
            pts := .from (pts.val.map slotOfBytes) (by simp [h.1]),
            is_complete := is_complete }
    else .Err .SerializationInvalid

/-- **Well-formedness predicate for `spqr::encoding::polynomial::PolyDecoder`**
• The in-memory states that survive a round trip.
• `pts_needed` fits into a `u32`, since `into_pb` truncates it.
• `PointsValid x.pts`: every slot has strictly increasing abscissae, since `from_pb` sorts and
  deduplicates. This is the `SortedSet<Pt>` invariant, which the Lean type does not enforce.
• No length bound: a sorted slot has at most 65536 points, so its encoding always fits into a
  `Vec`. `PolyDecoder` has no refine annotation, and the bound
  `pts.len() <= 2 * MAX_STORED_POLYNOMIAL_DEGREE_V1 + 1` that `into_pb` `hax_lib::assume!`s is
  deliberately omitted: `from_pb` does not check it, so it would falsify RT2a. -/
def WellFormed (x : PolyDecoder) : Prop :=
  x.pts_needed.val ≤ U32.max ∧ PointsValid x.pts

/-- **Canonicity predicate for `spqr::encoding::polynomial::PolyDecoder`**
• The protobuf states that survive a round trip, that is, the encodings of well-formed states.
• `polys` is `16`, since `from_pb` ignores it and `into_pb` writes `16`.
• `pts` holds exactly 16 byte strings, each of a length divisible by four, since `from_pb`
  rejects all others.
• The points of every byte string are sorted by abscissa without repetitions, since `from_pb`
  sorts and deduplicates. -/
def Canonical (pb : PolynomialDecoder) : Prop :=
  pb.polys = 16#u32 ∧ pb.pts.length = 16 ∧
    ∀ v ∈ pb.pts.val, v.length % 4 = 0 ∧ SlotSorted (ptsOfBytes v.val)

/-! ## Codec theorems

The list-level codec facts that the round-trip laws and the spec theorems rest on. -/

/-- The encoding of a point list is four times as long. -/
@[simp] theorem bytesOfPts_length (l : List Pt) : (bytesOfPts l).length = 4 * l.length := by
  induction l with
  | nil => rfl
  | cons p l ih => exact congrArg (· + 4) ih

/-- Decoding splits at every multiple of four bytes. -/
theorem ptsOfBytes_append (b c : List U8) (h : b.length % 4 = 0) :
    ptsOfBytes (b ++ c) = ptsOfBytes b ++ ptsOfBytes c :=
  match b, h with
  | [], _ => rfl
  | [_], h | [_, _], h | [_, _, _], h => nomatch h
  | _ :: _ :: _ :: _ :: rest, h =>
    congrArg (List.cons _) (ptsOfBytes_append rest c ((Nat.add_mod_right _ 4).symm.trans h))

/-- `ptsOfBytes` is a left inverse of `bytesOfPts`. -/
theorem ptsOfBytes_bytesOfPts (l : List Pt) : ptsOfBytes (bytesOfPts l) = l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨hx, hy⟩ := List.cons.inj (coeffsOfBytes_bytesOfCoeffs [p.x, p.y])
    exact congrArg₂ List.cons (congrArg₂ Pt.mk hx (List.cons.inj hy).1) ih

/-- `bytesOfPts` is a left inverse of `ptsOfBytes` on byte strings of length divisible by four. -/
theorem bytesOfPts_ptsOfBytes (b : List U8) (h : b.length % 4 = 0) :
    bytesOfPts (ptsOfBytes b) = b :=
  match b, h with
  | [], _ => rfl
  | [_], h | [_, _], h | [_, _, _], h => nomatch h
  | b0 :: b1 :: b2 :: b3 :: rest, h =>
    congrArg₂ (· ++ ·) (bytesOfCoeffs_coeffsOfBytes [b0, b1, b2, b3] (by simp))
      (bytesOfPts_ptsOfBytes rest ((Nat.add_mod_right _ 4).symm.trans h))

/-! ## Slot theorems

Sorted slots hold at most `65536` points, so they always fit into a vector, and stay sorted under
pushing; pushing the points of a sorted slot into the empty slot gives it back. -/

/-- A sorted slot holds at most `65536` points, one per abscissa. -/
theorem _root_.spqr.encoding.polynomial.PolyDecoder.SlotSorted.length_le {l : List Pt}
    (h : SlotSorted l) : l.length ≤ 65536 := by
  have hnd : (l.map fun p => (⟨p.x.value.val, p.x.value.hBounds⟩ : Fin 65536)).Nodup :=
    List.Pairwise.map _ (fun _ _ h => Fin.ne_of_val_ne (Nat.ne_of_lt h)) h
  exact (List.length_map _).symm.trans_le (hnd.length_le_card.trans_eq (Fintype.card_fin _))

/-- Inserting a point above every abscissa of a slot appends it. -/
theorem insertPt_eq_append {l : List Pt} {p : Pt} (h : ∀ q ∈ l, q.x.value.val < p.x.value.val) :
    insertPt l p = l ++ [p] := by
  rw [insertPt, List.filter_eq_self.mpr fun q hq => decide_eq_true (h q hq),
    List.filter_eq_nil_iff.mpr fun q hq h' => Nat.lt_asymm (h q hq) (of_decide_eq_true h')]

/-- Inserting a point into a sorted slot keeps it sorted. -/
theorem slotSorted_insertPt (l : List Pt) (p : Pt) (h : SlotSorted l) :
    SlotSorted (insertPt l p) := by
  simp only [insertPt, SlotSorted, List.pairwise_append, List.pairwise_cons, List.mem_filter,
    List.mem_cons, decide_eq_true_eq]
  exact ⟨List.Pairwise.filter _ h, ⟨fun r hr => hr.2, List.Pairwise.filter _ h⟩,
    fun a ha b hb => hb.elim (· ▸ ha.2) fun hb => lt_trans ha.2 hb.2⟩

/-- Pushing any points into a sorted slot gives a sorted slot. -/
theorem slotSorted_foldl_insertPt (l acc : List Pt) (h : SlotSorted acc) :
    SlotSorted (l.foldl insertPt acc) :=
  List.foldlRecOn _ insertPt h fun s hs p _ => slotSorted_insertPt s p hs

/-- Pushing the points of a sorted slot one after another into the empty slot gives them back. -/
theorem foldl_insertPt_nil {l : List Pt} (h : SlotSorted l) : l.foldl insertPt [] = l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l p ih =>
    obtain ⟨hl, -, hlt⟩ := List.pairwise_append.mp h
    rw [List.foldl_append, ih hl]
    exact insertPt_eq_append fun q hq => hlt q hq p (.head _)

/-- The points of a decoded slot: they are sorted, so they always fit into a vector. -/
theorem slotOfBytes_val (v : alloc.vec.Vec U8) :
    (slotOfBytes v).val = (ptsOfBytes v.val).foldl insertPt [] :=
  alloc.vec.Vec.ofList_val _ ((slotSorted_foldl_insertPt _ _ .nil).length_le.trans
    (le_trans (by decide) Usize.cMax_bound_concrete.1))

/-- The byte vector of a slot carries the whole byte string whenever that fits into a vector. -/
theorem bytesOfSlot_val (s : sorted_vec.SortedSet Pt) (h : 4 * s.length ≤ Usize.max) :
    (bytesOfSlot s).val = bytesOfPts s.val :=
  alloc.vec.Vec.ofList_val _ ((bytesOfPts_length _).trans_le h)

/-! ## Round-trip laws -/

/-- **Encoded well-formed in-memory states yield canonical protobuf states (RT1a) for
`spqr::encoding::polynomial::PolyDecoder`**
• Every well-formed in-memory state encodes to a canonical protobuf state. -/
theorem canonical_intoPb (x : PolyDecoder) (h : WellFormed x) : Canonical (intoPb x) := by
  obtain ⟨-, h⟩ := h
  rcases x with ⟨n, pts, c⟩
  have hpts := alloc.vec.Vec.ofList_val (pts.val.map bytesOfSlot)
    (((List.length_map ..).trans pts.property).trans_le
      ((UScalar.hrBounds _).trans_eq ((UScalar.rMax_eq_max _).trans UScalar.max_USize_eq)))
  refine ⟨rfl, (congrArg List.length hpts).trans ((List.length_map _).trans pts.property), ?_⟩
  simp only [intoPb, hpts, List.forall_mem_map]
  intro s hs
  simp [bytesOfSlot_val s ((Nat.mul_le_mul_left 4 (h s hs).length_le).trans
    (le_trans (by decide) Usize.cMax_bound_concrete.1)), ptsOfBytes_bytesOfPts, h s hs]

/-- **Round trip `fromPb ∘ intoPb` (RT1b) for `spqr::encoding::polynomial::PolyDecoder`**
• Every well-formed in-memory state survives encoding followed by decoding unchanged. -/
@[simp]
theorem roundtrip_fromPb_intoPb (x : PolyDecoder) (h : WellFormed x) :
    fromPb (intoPb x) = .Ok x := by
  obtain ⟨-, h16, hslots⟩ := canonical_intoPb x h
  rcases x with ⟨n, pts, c⟩
  obtain ⟨hn, hvalid⟩ := h
  rw [intoPb, fromPb, dite_eq_left ⟨h16, fun v hv => (hslots v hv).1⟩]
  simp only [core.result.Result.Ok.injEq, PolyDecoder.mk.injEq, and_true]
  refine ⟨UScalar.eq_of_val_eq (by
    rw [UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by simp [UScalarTy.numBits]),
      UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (Nat.lt_succ_of_le (U32.max_eq ▸ hn))]),
    Aeneas.Std.Array.ext _ _ ?_⟩
  rw [Array.from_val, alloc.vec.Vec.ofList_val _ (((List.length_map ..).trans pts.property).trans_le
      ((UScalar.hrBounds _).trans_eq ((UScalar.rMax_eq_max _).trans UScalar.max_USize_eq))),
    List.map_map, Function.comp_def]
  -- Slot by slot: decoding the encoding of a sorted slot gives the slot back.
  refine (List.map_congr_left fun s hs => alloc.vec.Vec.ext _ _ ?_).trans (List.map_id' _)
  rw [slotOfBytes_val, bytesOfSlot_val s ((Nat.mul_le_mul_left 4 (hvalid s hs).length_le).trans
      (le_trans (by decide) Usize.cMax_bound_concrete.1)), ptsOfBytes_bytesOfPts,
    foldl_insertPt_nil (hvalid s hs)]

/-- **Successfully decoded protobuf input states yield well-formed in-memory states (RT2a) for
`spqr::encoding::polynomial::PolyDecoder`**
• Every in-memory state the decoder successfully produces satisfies `WellFormed`. -/
theorem wellFormed_of_fromPb (pb : PolynomialDecoder) (x : PolyDecoder)
    (h : fromPb pb = .Ok x) : WellFormed x := by
  simp only [fromPb] at h
  split at h <;> cases h
  simp only [WellFormed, PointsValid, Array.from_val, List.forall_mem_map]
  exact ⟨(UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by simp [UScalarTy.numBits])).trans_le
      ((Nat.le_of_lt_succ (UScalar.hBounds _)).trans_eq U32.max_eq.symm),
    fun v _ => slotOfBytes_val v ▸ slotSorted_foldl_insertPt _ _ .nil⟩

/-- **Round trip `intoPb ∘ fromPb` (RT2b) for `spqr::encoding::polynomial::PolyDecoder`**
• Every canonical protobuf state survives decoding followed by encoding unchanged. -/
theorem roundtrip_intoPb_fromPb (pb : PolynomialDecoder) (h : Canonical pb) :
    ∃ x, fromPb pb = .Ok x ∧ intoPb x = pb := by
  obtain ⟨hpolys, h16, hslots⟩ := h
  rcases pb with ⟨i, polys, pts, c⟩
  rw [fromPb, dite_eq_left ⟨h16, fun v hv => (hslots v hv).1⟩]
  refine ⟨_, rfl, ?_⟩
  simp only [intoPb, Array.from_val, List.map_map, Function.comp_def, PolynomialDecoder.mk.injEq,
    and_true]
  have hi : (i.cast .Usize).val = i.val :=
    UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by simp [UScalarTy.numBits])
  refine ⟨UScalar.eq_of_val_eq ((UScalar.cast_val_mod_pow_of_inBounds_eq _ _
      (hi.trans_lt i.hBounds)).trans hi), hpolys.symm,
    (congrArg alloc.vec.Vec.ofList ?_).trans (alloc.vec.Vec.val_ofList pts)⟩
  -- Slot by slot: encoding the slot decoded from sorted four-byte points gives the bytes back.
  refine (List.map_congr_left fun v hv => ?_).trans (List.map_id' _)
  rw [bytesOfSlot, slotOfBytes_val, foldl_insertPt_nil (hslots v hv).2,
    bytesOfPts_ptsOfBytes _ (hslots v hv).1, alloc.vec.Vec.val_ofList]

end spqr.encoding.polynomial.PolyDecoder.FunctionalModels
