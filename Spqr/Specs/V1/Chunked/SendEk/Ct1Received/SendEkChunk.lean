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
`spqr::v1::chunked::send_ek::{spqr::v1::chunked::send_ek::Ct1Received}::send_ek_chunk`

`Ct1Received` is the state of the encapsulation-key-sending (A→B) side of the *chunked* V1
ratchet after A has received (erasure-decoded) B's first ciphertext `ct1`, while A is still
streaming its own encapsulation key `ek` to B in fixed-size chunks.  It wraps the corresponding
unchunked state `unchunked::EkSentCt1Received` (which carries the current `epoch : u64`
together with the `Authenticator`, the 2400-byte decapsulation key `dk`, and the 960-byte
`ct1`) and adds a `PolyEncoder` that erasure-codes the outgoing `ek` into chunks.

`Ct1Received::send_ek_chunk` produces the next chunk of the encoded encapsulation key.  It
destructures `self` into the unchunked state `uc` and the encoder `sending_ek`, calls
`Encoder::next_chunk` on the encoder, and rebuilds the state with the advanced encoder.  The
inner unchunked state `uc` is moved through untouched, so the epoch, the authenticator, the
decapsulation key `dk`, and the received `ct1` are preserved verbatim.  The state type is
unchanged by the transition: A keeps emitting `ek` chunks (each stamped with `uc.epoch` by
`States::send` as an `EkCt1Ack` message) until B's first `ct2` chunk arrives, at which point
`recv_ct2_chunk` moves the ratchet on to `EkSentCt1Received`.

Mathematically the chunk is the evaluation of the sixteen GF(2¹⁶) polynomials held by the
encoder at the point `x = idx`:  the `j`-th 16-bit word of the chunk data is
`polys[j](idx)` in `GF216 = GaloisField 2 16`, and the chunk is tagged with `index = idx`.  The
encoder's index is then wrapping-incremented modulo 2³².  If the encoder is still in the
`Points` phase it first interpolates the polynomials (Lagrange interpolation over the stored
points) before evaluating — this is all inherited from `PolyEncoder::next_chunk`.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 158:4-162:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr encoding.polynomial encoding.gf Polynomial

namespace spqr.v1.chunked.send_ek.Ct1Received

/-- **Spec theorem for `spqr.v1.chunked.send_ek.Ct1Received.send_ek_chunk`**:

• Takes a chunked `Ct1Received` state `self`, consisting of the unchunked inner state
  `self.uc : unchunked.send_ek.EkSentCt1Received` and the chunk encoder
  `self.sending_ek : PolyEncoder`.  In the original Rust source `self` is consumed by value;
  the Lean extraction mirrors this.
• Delegates to the polynomial encoder:
    `PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk self.sending_ek`
  which yields a pair `(chunk, sending_ek')`.
• Returns `({ self with sending_ek := sending_ek' }, chunk)`.

• The function succeeds under exactly the preconditions of `next_chunk_spec`:
    – `h_idx_fits`: the current encoder index fits in a `u16`
      (`self.sending_ek.idx.val ≤ U16.max`), so the cast performed by `next_chunk` is lossless.
      This restriction is inherited from `next_chunk_spec`: Rust truncates with
      `self.idx as u16` (spqr/src/encoding/polynomial.rs), so after 2¹⁶ unacknowledged chunks
      `chunk.index` wraps while `idx` keeps counting.  Those states are accepted by Rust but
      are outside this contract; the index relation would need to be stated modulo 2¹⁶ to cover
      them, which should be done in the supporting contract first;
    – `h_admissible`: if the encoder is still in the `Points` phase, every one of the sixteen
      point-vectors has one of the admissible lengths `0, 1, 3, 5, 30, 34, 36` so that Lagrange
      interpolation is well-defined;
    – `h_coeff_bound`: if the encoder is in the `Polys` phase, every polynomial has at most
      `Usize.max - 1` coefficients so that evaluation does not overflow.
• The unchunked state is carried through unchanged, so in particular
    `result.uc.epoch = self.uc.epoch`, `result.uc.auth = self.uc.auth`,
    `result.uc.dk = self.uc.dk`, and `result.uc.ct1 = self.uc.ct1`.

The result satisfies the postcondition:

  `result.uc = self.uc`
  `PolyEncoder.NextChunkPostCond self.sending_ek result.sending_ek chunk`

where `NextChunkPostCond` (defined once in `PolyEncoder.Defs` and shared verbatim with
`next_chunk_spec` and the `send_ct*_chunk` specs) states
`chunk.index.val = self.sending_ek.idx.val`, `chunk.data.length = 32`,
`result.sending_ek.idx.val = (self.sending_ek.idx.val + 1) % U32.size`, and the
phase-dependent encoder invariant:

  • `Polys polys` phase — the polynomials are left unchanged
    (`result.sending_ek.s = self.sending_ek.s`) and for every `j < 16` the `j`-th 16-bit
    big-endian word of the chunk is the evaluation of the `j`-th polynomial at the index:
      `chunkWord chunk.data j =
          polys[j].toGF216Poly.eval (self.sending_ek.idx.val.toGF216)`
  • `Points pts` phase — either the encoder stays in `Points` (cache hit) and every chunk word
    is the stored point `pts[j][idx]`, or it transitions to `Polys polys'` where
      `polys'[j].toGF216Poly =
          ∑ k < |pts[j]|, C (pts[j][k].toGF216) * scaledLagrangeBasis |pts[j]| k`,
    the coefficient count is bounded, and each chunk word is either a cache hit or an
    evaluation of the interpolant at `idx`

The proof unfolds `send_ek_chunk` and applies `next_chunk_spec` with the supplied hypotheses;
the `uc`-preservation conjunct is closed by reflexivity (`{ self with sending_ek }` leaves `uc`
syntactically untouched) and the remaining goal is exactly the inherited postcondition.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 158:4-162:5)
-/
@[step]
theorem send_ek_chunk_spec (self : Ct1Received)
    (h_idx_fits : self.sending_ek.idx.val ≤ U16.max)
    (h_admissible : ∀ pts, self.sending_ek.s = .Points pts →
        ∀ (j : Nat), j < 16 →
          let len := (pts[j]!).value.length
          len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
          len = 30 ∨ len = 34 ∨ len = 36)
    (h_coeff_bound : ∀ polys, self.sending_ek.s = .Polys polys →
        ∀ (j : Nat), j < 16 →
          (polys[j]!).coefficients.length + 1 ≤ Usize.max) :
    send_ek_chunk self ⦃ ((result, chunk) : Ct1Received × encoding.Chunk) =>
      result.uc = self.uc ∧
      PolyEncoder.NextChunkPostCond self.sending_ek result.sending_ek chunk ⦄ := by
  unfold send_ek_chunk
  step with PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk_spec self.sending_ek
    h_idx_fits h_admissible h_coeff_bound
  exact chunk_post

end spqr.v1.chunked.send_ek.Ct1Received
