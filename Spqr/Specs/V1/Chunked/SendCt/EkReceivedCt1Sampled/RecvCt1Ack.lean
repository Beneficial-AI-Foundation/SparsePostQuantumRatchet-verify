/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.V1.Unchunked.SendCt.Ct1SentEkReceived.SendCt2
public import Spqr.Specs.V1.Chunked.SendCt.SendCt2Encoder
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.Defs
import Spqr.Auxiliary.Aeneas.Vec
/-!
# Spec theorem for
`spqr::v1::chunked::send_ct::{spqr::v1::chunked::send_ct::EkReceivedCt1Sampled}::recv_ct1_ack`

`EkReceivedCt1Sampled` is the state of the ciphertext-sending (B→A) side of the *chunked* V1
ratchet after B has fully received (erasure-decoded) A's encapsulation key `ek` and has sampled
the first ciphertext `ct1`, which is still being streamed to A in fixed-size chunks.  It wraps
the corresponding unchunked state `Ct1SentEkReceived` (which carries the current `epoch : u64`
together with the `Authenticator`, the encapsulation state `es`, the complete `ek`, and `ct1`)
and adds a `PolyEncoder` that erasure-codes `ct1` into chunks.

`EkReceivedCt1Sampled::recv_ct1_ack` is called when A acknowledges receipt of `ct1`.  It:

  1. asserts that the incoming `epoch` matches `self.uc.epoch`;
  2. delegates to the unchunked `Ct1SentEkReceived::send_ct2`, which completes the ML-KEM-768
     encapsulation (producing the 128-byte `ct2`) and computes `mac = HMAC(mac_key, ct1 ‖ ct2)`;
  3. erasure-encodes `ct2 ‖ mac` into a `PolyEncoder` via `send_ct2_encoder`;
  4. returns the resulting `Ct2Sampled { uc, sending_ct2 }`.

The precondition `epoch = self.uc.epoch` is checked by `massert` (an `assert_eq!` in Rust).  The
transition consumes the `EkReceivedCt1Sampled` state and produces a `Ct2Sampled` state, advancing
the chunked send-side state machine.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 236:4-243:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr encoding.polynomial encoding.gf Polynomial
     Spqr.IncrementalMlkem768

namespace spqr.v1.chunked.send_ct.EkReceivedCt1Sampled

open List core.num.U64 authenticator.Authenticator in
/-- **Spec theorem for `spqr.v1.chunked.send_ct.EkReceivedCt1Sampled.recv_ct1_ack`**:

• Takes a chunked `EkReceivedCt1Sampled` state `self` and an `epoch : U64`.  In the Rust source,
  `self` is consumed by value and `epoch` is passed by value (`Epoch = u64`).
• Requires `epoch = self.uc.epoch` (checked by `massert`, reflecting `assert_eq!` in Rust).
• Delegates to `Ct1SentEkReceived.send_ct2` on the inner unchunked state `self.uc`, which
  performs the second ML-KEM-768 encapsulation step and computes the HMAC tag over the full
  ciphertext.
• Passes the resulting 128-byte `ct2` and 32-byte `mac` to `send_ct2_encoder`, which
  erasure-encodes `ct2 ‖ mac` into a `PolyEncoder` starting at index 0 in the `Points` phase
  with 16 point vectors of length 5 each.
• Returns a `Ct2Sampled` whose `.uc` records the advanced unchunked state (`Ct2Sent`) and whose
  `.sending_ct2` is the freshly built encoder.

The result satisfies the postcondition (inherited from `send_ct2_spec` and
`send_ct2_encoder_spec`):

  `result.uc.epoch = self.uc.epoch`
  `result.uc.auth  = self.uc.auth`
  `∃ ct2 mac,`
    `ct2.length = 128 ∧ Encaps2Post self.uc.ek self.uc.es ct2` — FIPS 203 round-2 ciphertext;
    `mac.length = MACSIZE ∧ mac = HMAC-SHA256(mac_key, MAC_CT_LABEL ‖ epoch ‖ ct1 ‖ ct2)`;
    `result.sending_ct2.idx = 0#u32`
    `∃ pts, result.sending_ct2.s = EncoderState.Points pts ∧`
           `(∀ j < 16, pts[j]!.value.length = 5) ∧`
           round-robin content: coefficient `k` of `pts[j]` is the big-endian byte pair at
           offset `2·(j + 16·k)` of `ct2 ‖ mac`.

So the encoder is pinned to the actual ciphertext and tag: an implementation encoding 160
arbitrary bytes, or a MAC over different data, is excluded.

The proof unfolds `recv_ct1_ack`, dispatches `massert` (trivial from `h_epoch`), then applies
`send_ct2_spec` and `send_ct2_encoder_spec` via `step*`.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 236:4-243:5)
-/
@[step]
theorem recv_ct1_ack_spec (self : EkReceivedCt1Sampled) (epoch : U64)
    (h_epoch : epoch = self.uc.epoch)
    (h_ek : self.uc.ek.length = 1152)
    (h_es : self.uc.es.length = 2080)
    (h_key : self.uc.auth.mac_key.length ≤ U32.max)
    (h_ct : self.uc.ct1.length + 128 + 43 ≤ U32.max) :
    recv_ct1_ack self epoch ⦃ (result : v1.chunked.send_ct.Ct2Sampled) =>
      result.uc.epoch = self.uc.epoch ∧
      result.uc.auth = self.uc.auth ∧
      ∃ (ct2 mac : alloc.vec.Vec U8),
        ct2.length = 128 ∧
        Encaps2Post self.uc.ek self.uc.es ct2 ∧
        mac.length = MACSIZE.val ∧
        (∃ data : Slice U8,
          data.val = MAC_CT_LABEL ++ to_be_bytes self.uc.epoch ++ (self.uc.ct1.val ++ ct2.val) ∧
          libcrux_hmac.hmac .Sha256 self.uc.auth.mac_key.deref data (some MACSIZE) = ok mac) ∧
        result.sending_ct2.idx = 0#u32 ∧
        ∃ pts : Array Point 16#usize,
          result.sending_ct2.s = EncoderState.Points pts ∧
          (∀ (j : Nat), j < 16 → pts[j]!.value.length = 5) ∧
          (∀ (j : Nat), j < 16 →
            ∀ (k : Nat), k < 5 →
              let msg := ct2.val ++ mac.val
              2 * (j + 16 * k) + 1 < 160 ∧
              (listToGF216Poly pts[j]!.value).coeff k =
                (256 * msg[2 * (j + 16 * k)]! + (msg[2 * (j + 16 * k) + 1]!).val).toGF216) ⦄ := by
  unfold recv_ct1_ack
  step with massert_spec _ h_epoch
  step with unchunked.send_ct.Ct1SentEkReceived.send_ct2_spec self.uc h_ek h_es h_key h_ct
    as ⟨uc, ct2, mac, h_uc_ep, h_uc_auth, h_ct2_len, h_enc, h_mac_len, data, h_data, h_hmac⟩
  step with send_ct2_encoder_spec (alloc.vec.Vec.deref ct2) (alloc.vec.Vec.deref mac)
    (by simpa [Slice.length, alloc.vec.Vec.deref_val] using h_ct2_len)
    (by simpa [Slice.length, alloc.vec.Vec.deref_val] using h_mac_len)
    as ⟨pe, h_idx, pts, h_s, h_lens, h_coeffs⟩
  refine ⟨h_uc_ep, h_uc_auth, ct2, mac, h_ct2_len, h_enc, h_mac_len, ⟨data, h_data, h_hmac⟩,
    h_idx, pts, h_s, h_lens, ?_⟩
  intro j hj k hk
  have := h_coeffs j hj k hk
  simpa only [alloc.vec.Vec.deref_val] using this

end spqr.v1.chunked.send_ct.EkReceivedCt1Sampled
