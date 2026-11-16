/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.AddChunk
public import Spqr.Specs.V1.Chunked.SendEk.EkSentCt1Received.RecvCt2Chunk
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.New
import Spqr.Specs.Authenticator.Authenticator.MACSIZE
import Spqr.Specs.Aeneas.ResultExpect
/-!
# Spec theorem for
`spqr::v1::chunked::send_ek::{spqr::v1::chunked::send_ek::Ct1Received}::recv_ct2_chunk`

`Ct1Received` is the state of the encapsulation-key-sending (A→B) side of the *chunked* V1
ratchet after A has received (erasure-decoded) B's first ciphertext `ct1`, while A is still
streaming its own encapsulation key `ek` to B in fixed-size chunks.  It wraps the unchunked
state `unchunked::EkSentCt1Received` (carrying the current `epoch : u64`, the `Authenticator`,
the 2400-byte decapsulation key `dk` and the 960-byte `ct1`) and adds a `PolyEncoder` that
erasure-codes the outgoing `ek`.

`Ct1Received::recv_ct2_chunk` is the transition triggered by the *first* chunk of B's second
ciphertext `ct2` (streamed together with the authentication tag as `ct2 ‖ mac`).  Its arrival
tells A that B has already received the complete `ek`, so A stops sending `ek` chunks: the
encoder `sending_ek` is dropped and replaced by a decoder for the incoming `ct2 ‖ mac`.  On
receipt of a 32-byte `Chunk` it:

  1. asserts `epoch == self.uc.epoch` (discharged by the hax contract
     `requires(epoch == self.uc.epoch)`);
  2. asserts that `CIPHERTEXT2_SIZE + MACSIZE = 128 + 32 = 160` is even (the
     `hax_lib::assert!`), which is what makes the following construction infallible;
  3. builds a fresh `PolyDecoder::new(CIPHERTEXT2_SIZE + MACSIZE)` — a decoder for `160` bytes,
     i.e. `160 / 2 = 80` GF(2¹⁶) symbols spread over `16` polynomials, with every polynomial
     initially holding no points — and unwraps it with
     `.expect("should be able to decode ct2+mac size")`, which can never panic because `160` is
     even;
  4. feeds the chunk to the fresh decoder (`receiving_ct2.add_chunk(chunk)`), which routes each
     of the 16 big-endian GF(2¹⁶) symbols of the chunk to polynomial `j` at x-coordinate
     `chunk.index` and inserts the resulting point into the corresponding (empty) sorted set —
     unless that polynomial already holds enough points;
  5. returns `EkSentCt1Received { uc: self.uc, receiving_ct2 }`.

The inner unchunked state `uc` is moved through untouched, so the epoch, the authenticator, the
decapsulation key `dk` and the received `ct1` are preserved verbatim.  The decoder of the new
state is the result of absorbing `chunk` into a fresh `160`-byte decoder; in particular it
satisfies the `#[hax_lib::refine]` struct invariant of `EkSentCt1Received`,
`receiving_ct2.get_pts_needed() == (CIPHERTEXT2_SIZE + MACSIZE) / 2 = 80`, it is not yet
complete, and every slot is `SlotSorted` (`PointsValid`) — exactly the hypotheses that the
follow-up transition `EkSentCt1Received::recv_ct2_chunk` requires of its state.

The value `128` of `CIPHERTEXT2_SIZE` is the premise `h_ct2_size`. `CIPHERTEXT2_SIZE_spec`
proves it.
All other callees (`MACSIZE`, `usize` arithmetic, `PolyDecoder::new`, `expect`, `add_chunk`)
are discharged by their registered specs.  The `h_push_cap` guard of `add_chunk_spec` is not
assumed: every slot of the fresh decoder is empty, so it holds trivially.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 165:4-180:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr encoding.polynomial encoding.gf

/- Helper definitions live in a CamelCase namespace (mirroring
`Spqr.V1.Chunked.SendEk.EkSentCt1Received` in `EkSentCt1Received/RecvCt2Chunk.lean`) so that
their full names satisfy the `defsWithUnderscore` linter; the spec theorems themselves stay in
the Rust-mirroring `spqr.v1.chunked.send_ek.Ct1Received` namespace. -/
namespace Spqr.V1.Chunked.SendEk.Ct1Received

open List in
/-- Characterisation of the fresh `ct2 ‖ mac` decoder built by `Ct1Received::recv_ct2_chunk`
*before* the first chunk is absorbed: it is `PolyDecoder::new(CIPHERTEXT2_SIZE + MACSIZE)`,
i.e. it needs `160 / 2 = 80` points, starts with all `16` polynomials empty and is not
complete.  (Counterpart of `freshHdrDecoder` for the `96`-byte header decoder.) -/
def freshCt2Decoder (pd : PolyDecoder) : Prop :=
  pd.pts_needed.val = 80 ∧
  pd.pts.val = replicate 16 default ∧
  pd.is_complete = false

/-- Postcondition of `Ct1Received::recv_ct2_chunk` as a predicate on the returned
`EkSentCt1Received` state:

  - the unchunked inner state is preserved verbatim (`result.uc = self.uc`);
  - the new decoder is obtained by absorbing `chunk` (per
    `Spqr.V1.Chunked.SendEk.EkSentCt1Received.addChunkPost`) into a fresh `160`-byte decoder
    `pd0` (per `freshCt2Decoder`);
  - every slot of the new decoder is `SlotSorted` (`PointsValid`). -/
def recvCt2ChunkPost (self : spqr.v1.chunked.send_ek.Ct1Received) (chunk : encoding.Chunk)
    (result : spqr.v1.chunked.send_ek.EkSentCt1Received) : Prop :=
  result.uc = self.uc ∧
  (∃ (pd0 : PolyDecoder),
    freshCt2Decoder pd0 ∧
    Spqr.V1.Chunked.SendEk.EkSentCt1Received.addChunkPost pd0 chunk result.receiving_ct2) ∧
  PolyDecoder.PointsValid result.receiving_ct2.pts

/-- After absorbing a single chunk into a fresh (all-empty) decoder, every slot holds at most
one point.  Thin bridge from the state-local `addChunkPost` (definitionally the shared
`PolyDecoder.Insts.SpqrEncodingDecoder.AddChunkPost`) to the generic
`AddChunkPost.slot_length_le_one_of_fresh`.  This is the fact the follow-up transition
`EkSentCt1Received::recv_ct2_chunk` needs to discharge its `h_push_cap` guard. -/
theorem slot_length_le_one_of_fresh (pd0 : PolyDecoder) (chunk : encoding.Chunk)
    (pd : PolyDecoder)
    (h_fresh : pd0.pts.val = List.replicate 16 default)
    (h_add : Spqr.V1.Chunked.SendEk.EkSentCt1Received.addChunkPost pd0 chunk pd) :
    ∀ (k : Nat), k < 16 → (pd.pts[k]!).length ≤ 1 :=
  PolyDecoder.Insts.SpqrEncodingDecoder.AddChunkPost.slot_length_le_one_of_fresh pd0 chunk pd
    h_fresh h_add

end Spqr.V1.Chunked.SendEk.Ct1Received

namespace spqr.v1.chunked.send_ek.Ct1Received

open Spqr.V1.Chunked.SendEk.Ct1Received

/-- **Spec theorem for `spqr.v1.chunked.send_ek.Ct1Received.recv_ct2_chunk`**:

• Takes a chunked `Ct1Received` state `self`, consisting of the unchunked inner state
  `self.uc : unchunked.send_ek.EkSentCt1Received` and the chunk encoder
  `self.sending_ek : PolyEncoder`, the epoch `epoch : U64` announced by the peer, and the
  received 32-byte `chunk`.  In the original Rust source `self` is consumed by value and
  `chunk` is passed by shared reference; after Aeneas extraction both are plain values.
• Checks `massert (epoch = self.uc.epoch)`, which succeeds because of `h_epoch`.
• Computes `CIPHERTEXT2_SIZE + MACSIZE = 160` (no overflow) and checks
  `massert (160 % 2 = 0)`, which succeeds by evaluation.
• Builds `PolyDecoder::new 160`, which is `Ok pd0` with `freshCt2Decoder pd0`
  (`pts_needed = 80`, all slots empty, `is_complete = false`) since `160` is even, and unwraps
  it with `expect` (never panics on `Ok`).
• Absorbs the chunk into the fresh decoder via `add_chunk`, obtaining `receiving_ct2` with
  `addChunkPost pd0 chunk receiving_ct2` and `PointsValid receiving_ct2.pts`.
• Returns `{ uc := self.uc, receiving_ct2 }`; the encoder `self.sending_ek` is dropped.

• Requires:
    – `h_epoch : epoch = self.uc.epoch` — the hax precondition, discharging the `assert_eq!`;
    – `h_overflow` — the `usize` guard of `add_chunk_spec`: the base index
      `chunk.index * 16 + 16` fits in a `usize`;
    – `h_ct2_size` — the value of `CIPHERTEXT2_SIZE` (`CIPHERTEXT2_SIZE_spec`).
  The `h_push_cap` guard of `add_chunk_spec` is *not* assumed: every slot of the fresh decoder
  is empty (`PolyDecoder.Insts.SpqrEncodingDecoder.push_cap_of_replicate_default`).  Under
  these hypotheses the call never panics.
• The transition introduces no epoch logic of its own: the unchunked state is untouched, so the
  epoch, the authenticator, `dk` and `ct1` of the result are those of `self`.

The result satisfies `recvCt2ChunkPost self chunk result`.

The proof unfolds `recv_ct2_chunk`, discharges the first assertion with `h_epoch`, runs
`h_ct2_size` and `MACSIZE_spec` to evaluate the size arithmetic to `160`, discharges the parity
assertion by evaluation, reduces `PolyDecoder::new 160` to its `Ok` branch via `new_spec`,
unwraps it with `expect_ok_spec`, and finally runs `add_chunk_spec` together with
`add_chunk_spec_valid` on the fresh decoder.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 165:4-180:5)
-/
@[step]
theorem recv_ct2_chunk_spec (self : Ct1Received) (epoch : U64) (chunk : encoding.Chunk)
    (h_epoch : epoch = self.uc.epoch)
    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_ct2_size : incremental_mlkem768.CIPHERTEXT2_SIZE ⦃ (r : Usize) => r.val = 128 ⦄) :
    recv_ct2_chunk self epoch chunk ⦃ (result : EkSentCt1Received) =>
      recvCt2ChunkPost self chunk result ⦄ := by
  unfold recv_ct2_chunk
  step with massert_spec _ h_epoch
  step with h_ct2_size as ⟨i, h_i⟩
  have h_i' : i = 128#usize := by scalar_tac
  subst h_i'
  step with Usize.add_spec (x := 128#usize) (y := authenticator.Authenticator.MACSIZE)
    (by simp only [authenticator.Authenticator.MACSIZE_spec]; scalar_tac) as ⟨i1, h_i1⟩
  have h_i1' : i1 = 160#usize := by
    simp only [authenticator.Authenticator.MACSIZE_spec] at h_i1; scalar_tac
  subst h_i1'
  step with Usize.rem_spec (x := 160#usize) (y := 2#usize) (by scalar_tac) as ⟨i2, h_i2⟩
  have h_i2' : i2 = 0#usize := by scalar_tac
  subst h_i2'
  step with massert_spec True trivial
  step with Usize.add_spec (x := 128#usize) (y := authenticator.Authenticator.MACSIZE)
    (by simp only [authenticator.Authenticator.MACSIZE_spec]; scalar_tac) as ⟨i3, h_i3⟩
  have h_i3' : i3 = 160#usize := by
    simp only [authenticator.Authenticator.MACSIZE_spec] at h_i3; scalar_tac
  subst h_i3'
  step with PolyDecoder.Insts.SpqrEncodingDecoder.new_spec 160#usize as ⟨decoder, h_new⟩
  simp only [↓reduceIte] at h_new
  cases decoder with
  | Err e => exact absurd h_new not_false
  | Ok pd0 =>
    obtain ⟨h_pts, h_vec, h_done⟩ := h_new
    step with core.result.Result.expect_ok_spec encoding.EncodingError.Insts.CoreFmtDebug
      pd0 _ as ⟨pd, h_pd⟩
    subst h_pd
    have h_valid0 : PolyDecoder.PointsValid pd.pts :=
      PolyDecoder.Insts.SpqrEncodingDecoder.PointsValid_replicate_default pd.pts h_vec
    step with WP.spec_and
      (PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_spec pd chunk
        h_overflow (PolyDecoder.Insts.SpqrEncodingDecoder.push_cap_of_replicate_default
          pd.pts h_vec))
      (PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_spec_valid pd chunk
        h_overflow (PolyDecoder.Insts.SpqrEncodingDecoder.push_cap_of_replicate_default
          pd.pts h_vec) h_valid0)
      as ⟨receiving_ct2, h_pn, h_ic, selfs, h_s0, h_s16, h_chain, h_valid'⟩
    simp only [recvCt2ChunkPost, true_and]
    refine ⟨⟨pd, ⟨?_, h_vec, h_done⟩, h_pn, h_ic, selfs, h_s0, h_s16, h_chain⟩, h_valid'⟩
    rw [h_pts]; rfl

/-- **Spec theorem for `spqr.v1.chunked.send_ek.Ct1Received.recv_ct2_chunk`**
(struct-invariant corollary):

Projection of `recv_ct2_chunk_spec` to the facts that the follow-up transition
`EkSentCt1Received::recv_ct2_chunk` (and the `#[hax_lib::refine]` invariant of the Rust
`EkSentCt1Received`) demand of the produced state:

  - `result.uc = self.uc` — the unchunked state is untouched;
  - `result.receiving_ct2.pts_needed.val = 80` — i.e. `(CIPHERTEXT2_SIZE + MACSIZE) / 2`;
  - `result.receiving_ct2.is_complete = false` — a single chunk never completes the decoder;
  - `PointsValid result.receiving_ct2.pts` — every slot is `SlotSorted`;
  - every slot of `result.receiving_ct2.pts` holds at most one point — which in particular
    discharges the `h_push_cap` guard (`length + 17 ≤ Usize.max`) of
    `EkSentCt1Received.recv_ct2_chunk_spec` for the next chunk.

`pts_needed` and `is_complete` are carried from the fresh decoder to the result because
`add_chunk` preserves both (`addChunkPost`); the slot bound is `slot_length_le_one_of_fresh`.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 165:4-180:5)
-/
theorem recv_ct2_chunk_spec_invariant (self : Ct1Received) (epoch : U64)
    (chunk : encoding.Chunk)
    (h_epoch : epoch = self.uc.epoch)
    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_ct2_size : incremental_mlkem768.CIPHERTEXT2_SIZE ⦃ (r : Usize) => r.val = 128 ⦄) :
    recv_ct2_chunk self epoch chunk ⦃ (result : EkSentCt1Received) =>
      result.uc = self.uc ∧
      result.receiving_ct2.pts_needed.val = 80 ∧
      result.receiving_ct2.is_complete = false ∧
      PolyDecoder.PointsValid result.receiving_ct2.pts ∧
      ∀ (k : Nat), k < 16 → (result.receiving_ct2.pts[k]!).length ≤ 1 ⦄ := by
  apply WP.spec_mono (recv_ct2_chunk_spec self epoch chunk h_epoch h_overflow h_ct2_size)
  intro result ⟨h_uc, ⟨pd0, ⟨h_pn0, h_vec0, h_ic0⟩, h_add⟩, h_valid⟩
  have h_pn := h_add.1
  have h_ic := h_add.2.1
  exact ⟨h_uc, by rw [h_pn, h_pn0], by rw [h_ic, h_ic0], h_valid,
    slot_length_le_one_of_fresh pd0 chunk result.receiving_ct2 h_vec0 h_add⟩

end spqr.v1.chunked.send_ek.Ct1Received
