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

/-- **Encoder-step postcondition**: the shared contract of `PolyEncoder::next_chunk` and of
the `send_ct*_chunk` wrappers that delegate to it.  `self` is the encoder *before* the step,
`self'` the encoder *after*, and `chunk` the emitted chunk.

* `chunk.index = self.idx`, `chunk.data.length = 32`, and `self'.idx = (self.idx + 1) mod 2³²`.
* `Polys polys` phase: the state is unchanged and every chunk word is `polys[j](idx)`.
* `Points pts` phase: exactly one of
  - **cache hit** — `idx < |pts[j]|` for every `j`, the state is unchanged
    (`self'.s = self.s`), and every chunk word is the stored point `pts[j][idx]`; or
  - **interpolation** — the state becomes `Polys polys'` where `polys'[j]` is the Lagrange
    interpolant of `pts[j]`, the coefficient counts are bounded, and every chunk word is either
    a stored point served before the transition or `polys'[j](idx)`.

Both `Points` alternatives constrain `chunk.data` and `self'.s`, so no branch is vacuous. -/
def NextChunkPostCond (self self' : PolyEncoder) (chunk : encoding.Chunk) : Prop :=
  chunk.index.val = self.idx.val ∧
  chunk.data.length = 32 ∧
  self'.idx.val = (self.idx.val + 1) % U32.size ∧
  match self.s with
  | .Polys polys =>
      self'.s = self.s ∧
      ∀ (j : Nat), j < 16 →
        chunkWord chunk.data j = (polys[j]!).toGF216Poly.eval (self.idx.val.toGF216)
  | .Points pts =>
      (self'.s = self.s ∧
        ∀ (j : Nat), j < 16 →
          self.idx.val < (pts[j]!).value.length ∧
          chunkWord chunk.data j = ((pts[j]!).value[self.idx.val]!).toGF216) ∨
      (∃ polys', self'.s = .Polys polys' ∧
        (∀ (j : Nat), j < 16 →
          polys'[j]!.toGF216Poly =
            ∑ k ∈ Finset.range (pts[j]!).value.length,
              C (((pts[j]!).value[k]!).toGF216) *
                scaledLagrangeBasis (alloc.vec.Vec.len ((pts[j]!).value)) k) ∧
        (∀ (j : Nat), j < 16 →
          (polys'[j]!).coefficients.length + 1 ≤ Usize.max) ∧
        (∀ (j : Nat), j < 16 →
          (self.idx.val < (pts[j]!).value.length ∧
            chunkWord chunk.data j = ((pts[j]!).value[self.idx.val]!).toGF216) ∨
          chunkWord chunk.data j = (polys'[j]!).toGF216Poly.eval (self.idx.val.toGF216)))

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
