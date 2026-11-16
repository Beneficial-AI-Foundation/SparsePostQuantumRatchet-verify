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
`spqr::v1::chunked::send_ek::{spqr::v1::chunked::send_ek::KeysSampled}::send_hdr_chunk`

`KeysSampled` is the state of the encapsulation-key-sending (A→B) side of the *chunked* V1
ratchet after A has sampled its new incremental ML-KEM key pair but before the header has been
fully streamed to B.  It wraps the corresponding unchunked state `unchunked::HeaderSent` (which
carries the current `epoch : u64` together with the `Authenticator`, the encapsulation key `ek`,
and the 2400-byte decapsulation key `dk`) and adds a `PolyEncoder` `sending_hdr` that
erasure-codes the 96-byte header‖MAC buffer into chunks.

`KeysSampled::send_hdr_chunk` produces the next chunk of the encoded header.  It destructures
`self` into the unchunked state `uc` and the encoder `sending_hdr`, calls `Encoder::next_chunk`
on the encoder, and rebuilds the state with the advanced encoder.  The inner unchunked state
`uc` is moved through untouched: the epoch, the authenticator, `ek`, and `dk` are preserved
verbatim, and the state type is unchanged by the transition — A keeps emitting header chunks
until B's first ciphertext chunk arrives (`recv_ct1_chunk`).  In the protocol the first header
chunk is emitted by `KeysUnsampled::send_hdr_chunk`, so on entry the encoder index is expected
to be at least 1; that fact is not yet established by a spec theorem and is not assumed here.

Mathematically the chunk is the evaluation of the sixteen GF(2¹⁶) polynomials held by the
encoder at the point `x = idx`:  the `j`-th 16-bit word of the chunk data is `polys[j](idx)` in
`GF216 = GaloisField 2 16`, and the chunk is tagged with `index = idx`.  The encoder's index is
then wrapping-incremented modulo 2³².  If the encoder is still in the `Points` phase it either
serves the stored point directly (cache hit, `idx < |pts[j]|`) or first interpolates the
polynomials (Lagrange interpolation over the stored points) and then evaluates — this is all
inherited from `PolyEncoder::next_chunk`.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 75:4-82:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr encoding.polynomial encoding.gf Polynomial

namespace spqr.v1.chunked.send_ek.KeysSampled

/-- **Spec theorem for `spqr.v1.chunked.send_ek.KeysSampled.send_hdr_chunk`**:

• Takes a chunked `KeysSampled` state `self`, consisting of the unchunked inner state
  `self.uc : unchunked.send_ek.HeaderSent` and the header chunk encoder
  `self.sending_hdr : PolyEncoder`.  In the original Rust source `self` is consumed by value;
  the Lean extraction mirrors this.
• Delegates to the polynomial encoder:
    `PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk self.sending_hdr`
  which yields a pair `(chunk, sending_hdr')`.
• Returns `({ self with sending_hdr := sending_hdr' }, chunk)`.

• The function succeeds under the preconditions of `next_chunk_spec`:
    – `h_admissible`: if the encoder is still in the `Points` phase, every one of the sixteen
      point-vectors has one of the admissible lengths `0, 1, 3, 5, 30, 34, 36` so that Lagrange
      interpolation is well-defined (an encoder built by `encode_bytes` from the 96-byte
      header‖MAC buffer is expected to have exactly `96 / 2 / 16 = 3` values per point-vector;
      establishing this at the call site is left to the `KeysUnsampled::send_hdr_chunk` spec);
    – `h_coeff_bound`: if the encoder is in the `Polys` phase, every polynomial has at most
      `Usize.max - 1` coefficients so that evaluation does not overflow.
• The unchunked state is carried through unchanged, so in particular
    `result.uc.epoch = self.uc.epoch`, `result.uc.auth = self.uc.auth`,
    `result.uc.ek = self.uc.ek`, and `result.uc.dk = self.uc.dk`.

Trust note: the proof inherits the `native_decide` auxiliary axioms of `chunk_at` /
`point_at_loop0.body` through `next_chunk_spec` (see issue #721).

The result satisfies the postcondition:

  `result.uc = self.uc`
  `PolyEncoder.NextChunkPostCond self.sending_hdr result.sending_hdr chunk`

where `NextChunkPostCond` (defined once in `PolyEncoder.Defs` and shared verbatim with
`next_chunk_spec`, `send_ek_chunk_spec`, and the `send_ct*_chunk` specs) states
`chunk.index.val = self.sending_hdr.wireIndex` (the counter mod 2¹⁶), `chunk.data.length = 32`,
`result.sending_hdr.idx.val = (self.sending_hdr.idx.val + 1) % U32.size`, and the
phase-dependent encoder invariant:

  • `Polys polys` phase — the polynomials are left unchanged
    (`result.sending_hdr.s = self.sending_hdr.s`) and for every `j < 16` the `j`-th 16-bit
    big-endian word of the chunk is the evaluation of the `j`-th polynomial at the index:
      `chunkWord chunk.data j =
          polys[j].toGF216Poly.eval (self.sending_hdr.wireIndex.toGF216)`
  • `Points pts` phase — either the encoder stays in `Points` (cache hit) and every chunk word
    is the stored point `pts[j][wireIndex]`, or it transitions to `Polys polys'` where
      `polys'[j].toGF216Poly =
          ∑ k < |pts[j]|, C (pts[j][k].toGF216) * scaledLagrangeBasis |pts[j]| k`,
    the coefficient count is bounded, and each chunk word is either a cache hit or an
    evaluation of the interpolant at the wire index

The proof unfolds `send_hdr_chunk` and applies `next_chunk_spec` with the supplied hypotheses;
the `uc`-preservation conjunct is closed by reflexivity (`{ self with sending_hdr }` leaves the
field syntactically untouched) and the remaining goal is exactly the inherited postcondition.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 75:4-82:5)
-/
@[step]
theorem send_hdr_chunk_spec (self : KeysSampled)
    (h_admissible : ∀ pts, self.sending_hdr.s = .Points pts →
        ∀ (j : Nat), j < 16 →
          let len := (pts[j]!).value.length
          len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
          len = 30 ∨ len = 34 ∨ len = 36)
    (h_coeff_bound : ∀ polys, self.sending_hdr.s = .Polys polys →
        ∀ (j : Nat), j < 16 →
          (polys[j]!).coefficients.length + 1 ≤ Usize.max) :
    send_hdr_chunk self ⦃ ((result, chunk) : KeysSampled × encoding.Chunk) =>
      result.uc = self.uc ∧
      PolyEncoder.NextChunkPostCond self.sending_hdr result.sending_hdr chunk ⦄ := by
  unfold send_hdr_chunk
  step with PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk_spec self.sending_hdr
    h_admissible h_coeff_bound
  exact chunk_post

end spqr.v1.chunked.send_ek.KeysSampled
