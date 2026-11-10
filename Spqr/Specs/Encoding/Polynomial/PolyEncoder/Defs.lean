/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong, Markus Dablander
-/
module

public import SrcTranslated.Funs
public import Spqr.Math.Gf16.Field
public import Spqr.Math.Gf2Poly.Basic
public import Spqr.Math.Poly.Identities.Basic
public import Spqr.Math.Poly.Lagrange.CompletePoints
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Order.Int.ConditionallyCompleteOrder
import Mathlib.Tactic.ComputeDegree
import Spqr.Math.Gf16.Irreducible

/-! # Postcondition predicates for `PolyEncoder`

The named postconditions that the `PolyEncoder` spec theorems are stated against.

-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf spqr.math.gf Polynomial

namespace spqr.encoding.polynomial.PolyEncoder

/-- Canonical `Inhabited` instance for `Point` (empty value vector): the filler for every
`[j]!` lookup on `Point` collections in the specs. -/
instance instInhabitedPoint : Inhabited encoding.polynomial.Point :=
  ⟨⟨alloc.vec.Vec.new _⟩⟩

/-- The `j`-th 16-bit big-endian word of a chunk payload, read as a `GF216` element. -/
noncomputable def chunkWord (data : List U8) (j : Nat) : GF216 :=
  Nat.toGF216 (256 * data[2 * j]! + data[2 * j + 1]!)

/-- The chunk index that `next_chunk` emits: the `u32` counter cast to `u16`. -/
def wireIndex (self : PolyEncoder) : Nat := self.idx.val % 2 ^ 16

/-- The postcondition of one `next_chunk` call. `self` is the encoder before the call,
`self'` the encoder after it, and `chunk` the emitted chunk. Every use of the index is the
wire index `self.wireIndex`. Only the counter update uses the full `u32` counter. -/
def NextChunkPostCond (self self' : PolyEncoder) (chunk : encoding.Chunk) : Prop :=
  chunk.index.val = self.wireIndex ∧
  chunk.data.length = 32 ∧
  self'.idx.val = (self.idx.val + 1) % U32.size ∧
  match self.s with
  | .Polys polys =>
      self'.s = self.s ∧
      ∀ (j : Nat), j < 16 →
        chunkWord chunk.data j = (polys[j]!).toGF216Poly.eval (self.wireIndex.toGF216)
  | .Points pts =>
      (self'.s = self.s ∧
        ∀ (j : Nat), j < 16 →
          self.wireIndex < (pts[j]!).value.length ∧
          chunkWord chunk.data j = ((pts[j]!).value[self.wireIndex]!).toGF216) ∨
      (∃ polys', self'.s = .Polys polys' ∧
        (∀ (j : Nat), j < 16 →
          polys'[j]!.toGF216Poly =
            ∑ k ∈ Finset.range (pts[j]!).value.length,
              C (((pts[j]!).value[k]!).toGF216) *
                scaledLagrangeBasis (alloc.vec.Vec.len ((pts[j]!).value)) k) ∧
        (∀ (j : Nat), j < 16 →
          (polys'[j]!).coefficients.length + 1 ≤ Usize.max) ∧
        (∀ (j : Nat), j < 16 →
          (self.wireIndex < (pts[j]!).value.length ∧
            chunkWord chunk.data j = ((pts[j]!).value[self.wireIndex]!).toGF216) ∨
          chunkWord chunk.data j = (polys'[j]!).toGF216Poly.eval (self.wireIndex.toGF216)))

/-- The premises of `next_chunk_spec`: in the `Points` phase every point vector has an
admissible interpolation size, and in the `Polys` phase every coefficient count is bounded. -/
def NextChunkReady (self : PolyEncoder) : Prop :=
  (∀ pts, self.s = .Points pts →
    ∀ (j : Nat), j < 16 →
      let len := (pts[j]!).value.length
      len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨ len = 30 ∨ len = 34 ∨ len = 36) ∧
  (∀ polys, self.s = .Polys polys →
    ∀ (j : Nat), j < 16 → (polys[j]!).coefficients.length + 1 ≤ Usize.max)

/-- `n` consecutive `next_chunk` calls on one encoder, returning the chunks in call order. -/
def nextChunks : Nat → PolyEncoder → Result (List encoding.Chunk × PolyEncoder)
  | 0, e => ok ([], e)
  | n + 1, e => do
    let (c, e₁) ← Insts.SpqrEncodingEncoder.next_chunk e
    let (cs, e₂) ← nextChunks n e₁
    ok (c :: cs, e₂)

/-- **Postcondition predicate for `PolyEncoder.into_pb`**

The postcondition of `into_pb_spec_postcond`, the byte-level stepping stone to `into_pb_spec`:
the serialization identities together with the derived GF(2¹⁶) and binary-polynomial
identities. -/
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

/-- Postcondition of `from_pb_spec_postcond`, the byte-level stepping stone to `from_pb_spec`.
Reusage of `IntoPbPostCond` pins `from_pb` down as the inverse of `into_pb`; this avoids
restating the entire byte layout. -/
def FromPbPostCond (pb : proto.pq_ratchet.PolynomialEncoder)
    (result : core.result.Result PolyEncoder PolynomialError) : Prop :=
  if FromPbWellFormed pb then
    match result with
    | core.result.Result.Ok encoder => IntoPbPostCond encoder pb
    | core.result.Result.Err _ => False
  else result = core.result.Result.Err PolynomialError.SerializationInvalid

end spqr.encoding.polynomial.PolyEncoder
