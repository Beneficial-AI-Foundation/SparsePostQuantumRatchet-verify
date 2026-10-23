/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.NextChunk
public import Spqr.Math.Poly.Lagrange.CompletePoints
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.Defs
/-!
# Spec theorem for
`spqr::v1::chunked::send_ct::{spqr::v1::chunked::send_ct::EkReceivedCt1Sampled}::send_ct1_chunk`

State after `ek` is fully received and `ct1` sampled; wraps unchunked `Ct1SentEkReceived` plus
a `PolyEncoder` for `ct1`. `send_ct1_chunk` calls `next_chunk` on the encoder, emits one chunk,
advances the index, and passes the unchunked state through unchanged. No decoder is needed
(unlike `Ct1Sampled::send_ct1_chunk`) since `ek` reception is complete.

Each chunk evaluates the 16 GF(2¹⁶) polynomials at `x = idx`; the encoder index then
wrapping-increments mod 2³². In the `Points` phase, Lagrange interpolation precedes evaluation.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 226:4-233:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr encoding.polynomial encoding.gf Polynomial

namespace spqr.v1.chunked.send_ct.EkReceivedCt1Sampled

/-- **Spec theorem for `spqr.v1.chunked.send_ct.EkReceivedCt1Sampled.send_ct1_chunk`**:

Calls `next_chunk` on `self.sending_ct1`, returns the updated encoder with `self.uc` unchanged.

Preconditions (from `next_chunk_spec`):
- `h_idx_fits`: encoder index ≤ `U16.max`.
- `h_admissible`: in `Points` phase, each point-vector length ∈ `{0,1,3,5,30,34,36}`.
- `h_coeff_bound`: in `Polys` phase, each polynomial has ≤ `Usize.max - 1` coefficients.

Postconditions: `result.uc = self.uc`, `chunk.index.val = self.sending_ct1.idx.val`,
`chunk.data.length = 32`, index increments mod `U32.size`, plus the phase-dependent
encoder invariant from `next_chunk_spec` (polynomial evaluations or Lagrange interpolants). -/
@[step]
theorem send_ct1_chunk_spec (self : EkReceivedCt1Sampled)
    (h_idx_fits : self.sending_ct1.idx.val ≤ U16.max)
    (h_admissible : ∀ pts, self.sending_ct1.s = .Points pts →
        ∀ (j : Nat), j < 16 →
          let len := (pts[j]!).value.length
          len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
          len = 30 ∨ len = 34 ∨ len = 36)
    (h_coeff_bound : ∀ polys, self.sending_ct1.s = .Polys polys →
        ∀ (j : Nat), j < 16 →
          (polys[j]!).coefficients.length + 1 ≤ Usize.max) :
    send_ct1_chunk self ⦃ ((result, chunk) : EkReceivedCt1Sampled × encoding.Chunk) =>
      result.uc = self.uc ∧
      chunk.index.val = self.sending_ct1.idx.val ∧
      chunk.data.length = 32 ∧
      result.sending_ct1.idx.val = (self.sending_ct1.idx.val + 1) % U32.size ∧
      match self.sending_ct1.s with
      | .Polys polys =>
          result.sending_ct1.s = self.sending_ct1.s ∧
          ∀ (j : Nat), j < 16 →
            Nat.toGF216 (256 * chunk.data[2 * j]! + chunk.data[2 * j + 1]!) =
              (polys[j]!).toGF216Poly.eval (self.sending_ct1.idx.val.toGF216)
      | .Points pts =>
          ∀ polys', result.sending_ct1.s = .Polys polys' →
            ∀ (j : Nat), j < 16 →
              polys'[j]!.toGF216Poly =
                ∑ k ∈ Finset.range (pts[j]!).value.length,
                  C (((pts[j]!).value[k]!).toGF216) *
                    scaledLagrangeBasis (alloc.vec.Vec.len ((pts[j]!).value)) k ⦄ := by
  unfold send_ct1_chunk
  step with PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk_spec self.sending_ct1
    h_idx_fits h_admissible h_coeff_bound
  exact chunk_post

end spqr.v1.chunked.send_ct.EkReceivedCt1Sampled
