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
`spqr::v1::chunked::send_ct::{spqr::v1::chunked::send_ct::Ct2Sampled}::send_ct2_chunk`

`Ct2Sampled` wraps unchunked `Ct2Sent` plus a `PolyEncoder` that erasure-codes `ct2 ‖ mac`.
`send_ct2_chunk` calls `next_chunk` on the encoder, returns the chunk, and advances the encoder
while leaving the unchunked state unchanged. Each chunk word is `polys[j](idx)` in GF(2¹⁶);
if still in `Points` phase, Lagrange interpolation is performed first.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 288:4-295:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr encoding.polynomial encoding.gf Polynomial

namespace spqr.v1.chunked.send_ct.Ct2Sampled

/-- **Spec theorem for `spqr.v1.chunked.send_ct.Ct2Sampled.send_ct2_chunk`**:

Unfolds `send_ct2_chunk` and delegates to `next_chunk_spec`. Preconditions:
- `h_idx_fits`: encoder index fits in `u16`.
- `h_admissible`: in `Points` phase, each point-vector length ∈ `{0,1,3,5,30,34,36}`.
- `h_coeff_bound`: in `Polys` phase, each polynomial has ≤ `Usize.max - 1` coefficients.

Postcondition: `result.uc = self.uc`, `chunk.index = idx`, `chunk.data.length = 32`,
encoder index increments mod 2³², plus the phase-dependent invariant from `next_chunk_spec`
(`Polys`: chunk words = polynomial evaluations; `Points`: either stayed in Points with
chunk bytes = stored points, or transitioned to Polys with Lagrange interpolation identity). -/
@[step]
theorem send_ct2_chunk_spec (self : Ct2Sampled)
    (h_idx_fits : self.sending_ct2.idx.val ≤ U16.max)
    (h_admissible : ∀ pts, self.sending_ct2.s = .Points pts →
        ∀ (j : Nat), j < 16 →
          let len := (pts[j]!).value.length
          len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
          len = 30 ∨ len = 34 ∨ len = 36)
    (h_coeff_bound : ∀ polys, self.sending_ct2.s = .Polys polys →
        ∀ (j : Nat), j < 16 →
          (polys[j]!).coefficients.length + 1 ≤ Usize.max) :
    send_ct2_chunk self ⦃ ((result, chunk) : Ct2Sampled × encoding.Chunk) =>
      result.uc = self.uc ∧
      chunk.index.val = self.sending_ct2.idx.val ∧
      chunk.data.length = 32 ∧
      result.sending_ct2.idx.val = (self.sending_ct2.idx.val + 1) % U32.size ∧
      match self.sending_ct2.s with
      | .Polys polys =>
          result.sending_ct2.s = self.sending_ct2.s ∧
          ∀ (j : Nat), j < 16 →
            Nat.toGF216 (256 * chunk.data[2 * j]! + chunk.data[2 * j + 1]!) =
              (polys[j]!).toGF216Poly.eval (self.sending_ct2.idx.val.toGF216)
      | .Points pts =>
          -- Either stayed in Points (cache hit) with constrained bytes …
          (result.sending_ct2.s = self.sending_ct2.s ∧
            ∀ (j : Nat), j < 16 →
              self.sending_ct2.idx.val < (pts[j]!).value.length ∧
              Nat.toGF216 (256 * chunk.data[2 * j]! + chunk.data[2 * j + 1]!) =
                ((pts[j]!).value[self.sending_ct2.idx.val]!).toGF216) ∨
          -- … or transitioned to Polys with Lagrange identity
          (∃ polys', result.sending_ct2.s = .Polys polys' ∧
            (∀ (j : Nat), j < 16 →
              polys'[j]!.toGF216Poly =
                ∑ k ∈ Finset.range (pts[j]!).value.length,
                  C (((pts[j]!).value[k]!).toGF216) *
                    scaledLagrangeBasis (alloc.vec.Vec.len ((pts[j]!).value)) k) ∧
            (∀ (j : Nat), j < 16 →
              (polys'[j]!).coefficients.length + 1 ≤ Usize.max)) ⦄ := by
  unfold send_ct2_chunk
  step with PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk_spec self.sending_ct2
    h_idx_fits h_admissible h_coeff_bound
  exact chunk_post

end spqr.v1.chunked.send_ct.Ct2Sampled
