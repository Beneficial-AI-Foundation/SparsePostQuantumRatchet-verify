/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.NextChunk
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.Defs
/-!
# Spec theorem for
`spqr::v1::chunked::send_ct::{spqr::v1::chunked::send_ct::Ct2Sampled}::send_ct2_chunk`

`Ct2Sampled` wraps unchunked `Ct2Sent` plus a `PolyEncoder` that erasure-codes `ct2 ‖ mac`.
`send_ct2_chunk` calls `next_chunk` on the encoder, returns the chunk, and advances the encoder
while leaving the unchunked state unchanged. Each chunk word is `polys[j](idx)` in GF(2¹⁶).
If still in `Points` phase, the stored point `pts[j][idx]` is served and the state stays
`Points` while `idx` is below the stored point count; Lagrange interpolation (and the switch
to `Polys`) only happens once `idx` reaches it (src/encoding/polynomial.rs:646–650).

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 288:4-295:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr encoding.polynomial encoding.gf Polynomial

namespace spqr.v1.chunked.send_ct.Ct2Sampled

/-- **Spec theorem for `spqr.v1.chunked.send_ct.Ct2Sampled.send_ct2_chunk`**:

Unfolds `send_ct2_chunk` and delegates to `next_chunk_spec`. Preconditions:
- `h_idx_fits`: encoder index fits in `u16`. Rust's `self.idx as u16`
  (src/encoding/polynomial.rs:759) truncates silently, so indices ≥ 2¹⁶ (reachable only after
  65 536 chunks of a single `ct2`) are deliberately out of scope rather than an error case.
- `h_admissible`: in `Points` phase, each point-vector length ∈ `{0,1,3,5,30,34,36}`. The
  encoder built by `send_ct2_encoder` encodes `ct2 ‖ mac` (128 + 32 bytes = 80 points), so
  `encode_bytes_spec` gives every `pts[j]` length 5.
- `h_coeff_bound`: in `Polys` phase, each polynomial has ≤ `Usize.max - 1` coefficients.

Trust note: the proof inherits the `native_decide` auxiliary axioms of `chunk_at` /
`point_at_loop0.body` through `next_chunk_spec` (see issue #721).

Postcondition: `result.uc = self.uc` together with
`PolyEncoder.NextChunkPostCond self.sending_ct2 result.sending_ct2 chunk`, the predicate
shared with `next_chunk_spec` and `send_ct1_chunk_spec`: `chunk.index = idx`,
`chunk.data.length = 32`, encoder index increments mod 2³², and the phase-dependent invariant
(`Polys`: state unchanged, chunk words = polynomial evaluations; `Points`: either stayed in
Points with chunk words = stored points, or transitioned to Polys with the Lagrange
interpolation identity, where each chunk word is either a stored point served before the
transition or an evaluation of the interpolated polynomial at `idx`). -/
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
      PolyEncoder.NextChunkPostCond self.sending_ct2 result.sending_ct2 chunk ⦄ := by
  unfold send_ct2_chunk
  step with PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk_spec self.sending_ct2
    h_idx_fits h_admissible h_coeff_bound
  exact chunk_post

end spqr.v1.chunked.send_ct.Ct2Sampled
