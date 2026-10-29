/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.EncodeBytes
import Spqr.Specs.Aeneas.VecExtendFromSlice
import Spqr.Specs.Aeneas.ResultExpect
import Spqr.Auxiliary.Aeneas.Vec
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.Defs
/-!
# Spec theorem for `spqr::v1::chunked::send_ct::send_ct2_encoder`

`send_ct2_encoder` is the helper used by every transition of the *chunked* V1 ciphertext-sending
(B→A) side that samples the second ciphertext half.  Given the 128-byte second half `ct2` of an
ML-KEM-768 ciphertext and the 32-byte HMAC `mac` over the full ciphertext, it

  1. copies `ct2` into a fresh `Vec<u8>` (`ct2.to_vec()`);
  2. appends `mac` (`msg.extend_from_slice(mac)`), yielding the 160-byte message
       `msg = ct2 ‖ mac`;
  3. erasure-encodes `msg` with `PolyEncoder::encode_bytes`, which splits it into 80 big-endian
     GF(2¹⁶) symbols and deals them round-robin into 16 `Point` value vectors;
  4. `expect`s the result — infallible here, since 160 is even and far below the `2¹⁶ × 16`
     length cap.

Because `80 = 16 · 5` exactly, every one of the 16 points receives precisely 5 symbols, with
no remainder.  Symbol `k` of point `j` is the byte pair at message offset `2·(j + 16·k)`, which
for `j + 16·k < 64` lies inside `ct2` and for `j + 16·k ≥ 64` lies inside `mac`.

The Rust function carries the hax precondition
`ct2.len() == 128 && mac.len() == Authenticator::MACSIZE`, which is reflected verbatim as the
hypotheses `h_ct2` and `h_mac` below.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 159:0-163:1)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr encoding.polynomial encoding.gf Polynomial

namespace spqr.v1.chunked.send_ct

/-- **Spec theorem for `spqr.v1.chunked.send_ct.send_ct2_encoder`**:

• Takes two byte slices: the 128-byte second ciphertext half `ct2` and the 32-byte
  authenticator tag `mac` (`Authenticator::MACSIZE = 32`).
• Builds `msg = ct2.to_vec()` and extends it with `mac`:
    `alloc.slice.Slice.to_vec CloneU8 ct2` then `Vec.extend_from_slice CloneU8 msg mac`
  so that `msg1.val = ct2.val ++ mac.val` with `msg1.length = 160`.
• Encodes the dereferenced message with
    `PolyEncoder.Insts.SpqrEncodingEncoder.encode_bytes (Vec.deref msg1)`
  and unwraps the result with `core.result.Result.expect`.

• The function always succeeds (no panic) under the stated length preconditions: the
  `extend_from_slice` overflow guard is trivially satisfied (`128 + 32 ≤ Usize.max`), the
  message length `160` is even and ≤ `2^16 * 16`, so `encode_bytes` returns `Ok`, and `expect`
  on an `Ok` value is the identity.
• The returned encoder starts at index `0` and is in the `Points` phase:
    `result.idx = 0#u32` and `result.s = EncoderState.Points pts`.
• **Round-robin length**: since `160 / 2 = 80 = 16 · 5`, every point holds exactly 5 symbols:
    `∀ j < 16, pts[j]!.value.length = 5`.
• **Round-robin content**: writing `msg = ct2.val ++ mac.val`, coefficient `k` of the GF(2¹⁶)
  polynomial read off `pts[j]!.value` is the big-endian decoding of the byte pair at offset
  `2·(j + 16·k)`:
    `(listToGF216Poly pts[j]!.value).coeff k =
        (256 * msg[2 * (j + 16 * k)]! + msg[2 * (j + 16 * k) + 1]!).toGF216`
  with `2 * (j + 16 * k) + 1 < 160` for every `k < 5`.

The proof unfolds `send_ct2_encoder`, lets `step*` discharge `to_vec_spec`,
`extend_from_slice_U8_spec` and `encode_bytes_spec`, rewrites the message length to `160`,
rules out the `Err` / `Polys` branches (which `encode_bytes_spec` makes contradictory), and
finishes with `expect_ok_spec`.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 159:0-163:1)
-/
@[step]
theorem send_ct2_encoder_spec (ct2 mac : Slice U8)
    (h_ct2 : ct2.length = 128)
    (h_mac : mac.length = authenticator.Authenticator.MACSIZE.val) :
    send_ct2_encoder ct2 mac ⦃ (result : PolyEncoder) =>
      result.idx = 0#u32 ∧
      ∃ pts : Array Point 16#usize,
        result.s = EncoderState.Points pts ∧
        (∀ (j : Nat), j < 16 → pts[j]!.value.length = 5) ∧
        (∀ (j : Nat), j < 16 →
          ∀ (k : Nat), k < 5 →
            let msg := ct2.val ++ mac.val
            2 * (j + 16 * k) + 1 < 160 ∧
            (listToGF216Poly pts[j]!.value).coeff k =
              (256 * msg[2 * (j + 16 * k)]! + (msg[2 * (j + 16 * k) + 1]!).val).toGF216) ⦄ := by
  unfold send_ct2_encoder
  have h_mac' : mac.length = 32 := by
    simpa [authenticator.Authenticator.MACSIZE] using h_mac
  step with alloc.slice.Slice.to_vec_spec core.clone.CloneU8 ct2 (by intros _ _; rfl)
  have h_msg_val : msg.val = ct2.val := by rw [ct2_post]; rfl
  have h_msg_len : msg.length = 128 := by
    simp only [alloc.vec.Vec.length, h_msg_val]; exact h_ct2
  step with alloc.vec.Vec.extend_from_slice_U8_spec msg mac
    (by rw [h_msg_len, h_mac']; scalar_tac)
  have h_msg : (alloc.vec.Vec.deref msg1).val = ct2.val ++ mac.val := by
    simp only [alloc.vec.Vec.deref_val, msg1_post, h_msg_val]
  have h_len : (alloc.vec.Vec.deref msg1).length = 160 := by
    have h1 : ct2.val.length = 128 := h_ct2
    have h2 : mac.val.length = 32 := h_mac'
    simp only [Slice.length, h_msg, List.length_append, h1, h2]
  step
  simp only [h_len] at r_post
  cases r with
  | Err e => exact absurd r_post not_false
  | Ok pe =>
    obtain ⟨idx, s⟩ := pe
    cases s with
    | Polys polys => exact absurd r_post not_false
    | Points pts =>
      obtain ⟨h_idx, h_lens, h_coeffs⟩ := r_post
      step with core.result.Result.expect_ok_spec as ⟨res, h_res⟩
      subst h_res
      refine ⟨h_idx, pts, rfl, ?_, ?_⟩
      · intro j hj
        have := h_lens j hj
        simpa using this
      · intro j hj k hk
        have h_len_j := h_lens j hj
        simp only [Nat.reduceDiv, Nat.reduceMod, Nat.not_lt_zero, ↓reduceIte] at h_len_j
        have := h_coeffs j hj k (by omega)
        simpa [h_msg] using this

end spqr.v1.chunked.send_ct
