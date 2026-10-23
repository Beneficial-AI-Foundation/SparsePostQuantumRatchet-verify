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

`EkReceivedCt1Sampled` is the state of the ciphertext-sending (B→A) side of the *chunked* V1
ratchet after B has fully received (erasure-decoded) A's encapsulation key `ek` and has sampled
the first ciphertext `ct1`, which is still being streamed to A in fixed-size chunks.  It wraps
the corresponding unchunked state `Ct1SentEkReceived` (which carries the current `epoch : u64`
together with the `Authenticator`, the encapsulation state `es`, the complete `ek`, and `ct1`)
and adds a `PolyEncoder` that erasure-codes `ct1` into chunks.

`EkReceivedCt1Sampled::send_ct1_chunk` produces the next chunk of the encoded ciphertext.  It
destructures `self` into the unchunked state `uc` and the encoder `sending_ct1`, calls
`Encoder::next_chunk` on the encoder, and rebuilds the state with the advanced encoder.  The
inner unchunked state `uc` is moved through untouched, so the epoch, the authenticator, the
encapsulation state, `ek`, and `ct1` are all preserved verbatim.  Since `ek` has already been
fully received there is no decoder to carry along (in contrast to `Ct1Sampled::send_ct1_chunk`,
which additionally threads a `receiving_ek` decoder through), and the state type is unchanged
by the transition: B keeps emitting `ct1` chunks until A acknowledges `ct1`.

Mathematically the chunk is the evaluation of the sixteen GF(2¹⁶) polynomials held by the
encoder at the point `x = idx`:  the `j`-th 16-bit word of the chunk data is
`polys[j](idx)` in `GF216 = GaloisField 2 16`, and the chunk is tagged with `index = idx`.  The
encoder's index is then wrapping-incremented modulo 2³².  If the encoder is still in the
`Points` phase it first interpolates the polynomials (Lagrange interpolation over the stored
points) before evaluating — this is all inherited from `PolyEncoder::next_chunk`.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 226:4-233:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr encoding.polynomial encoding.gf Polynomial

namespace spqr.v1.chunked.send_ct.EkReceivedCt1Sampled

/-- **Spec theorem for `spqr.v1.chunked.send_ct.EkReceivedCt1Sampled.send_ct1_chunk`**:

• Takes a chunked `EkReceivedCt1Sampled` state `self`, consisting of the unchunked inner state
  `self.uc : unchunked.send_ct.Ct1SentEkReceived` and the chunk encoder
  `self.sending_ct1 : PolyEncoder`.  In the original Rust source `self` is consumed by value;
  the Lean extraction mirrors this.
• Delegates to the polynomial encoder:
    `PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk self.sending_ct1`
  which yields a pair `(chunk, sending_ct1')`.
• Returns `({ self with sending_ct1 := sending_ct1' }, chunk)`.

• The function succeeds under exactly the preconditions of `next_chunk_spec`:
    – `h_idx_fits`: the current encoder index fits in a `u16`
      (`self.sending_ct1.idx.val ≤ U16.max`), so the cast performed by `next_chunk` is lossless;
    – `h_admissible`: if the encoder is still in the `Points` phase, every one of the sixteen
      point-vectors has one of the admissible lengths `0, 1, 3, 5, 30, 34, 36` so that Lagrange
      interpolation is well-defined;
    – `h_coeff_bound`: if the encoder is in the `Polys` phase, every polynomial has at most
      `Usize.max - 1` coefficients so that evaluation does not overflow.
• The unchunked state is carried through unchanged, so in particular
    `result.uc.epoch = self.uc.epoch`, `result.uc.auth = self.uc.auth`,
    `result.uc.es = self.uc.es`, `result.uc.ek = self.uc.ek`, and `result.uc.ct1 = self.uc.ct1`.

The result satisfies the postcondition:

  `result.uc = self.uc`
  `chunk.index.val = self.sending_ct1.idx.val`
  `chunk.data.length = 32`
  `result.sending_ct1.idx.val = (self.sending_ct1.idx.val + 1) % U32.size`

together with the phase-dependent encoder invariant inherited from `next_chunk_spec`:

  • `Polys polys` phase — the polynomials are left unchanged
    (`result.sending_ct1.s = self.sending_ct1.s`) and for every `j < 16` the `j`-th 16-bit
    big-endian word of the chunk is the evaluation of the `j`-th polynomial at the index:
      `(256 * chunk.data[2j] + chunk.data[2j+1]).toGF216 =
          polys[j].toGF216Poly.eval (self.sending_ct1.idx.val.toGF216)`
  • `Points pts` phase — whatever polynomials `polys'` the encoder holds afterwards are the
    scaled-Lagrange interpolants of the stored points:
      `polys'[j].toGF216Poly =
          ∑ k < |pts[j]|, C (pts[j][k].toGF216) * scaledLagrangeBasis |pts[j]| k`

The proof unfolds `send_ct1_chunk` and applies `next_chunk_spec` with the supplied hypotheses;
the `uc`-preservation conjunct is closed by reflexivity (`{ self with sending_ct1 }` leaves `uc`
syntactically untouched) and the remaining goal is exactly the inherited postcondition.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 226:4-233:5)
-/
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

