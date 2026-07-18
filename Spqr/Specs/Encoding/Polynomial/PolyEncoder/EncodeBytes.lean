/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.EncodeBytesBase

/-!
# Spec theorem for `{spqr::encoding::Encoder for PolyEncoder}::encode_bytes`

`encode_bytes` is the `Encoder` trait impl for `PolyEncoder`, delegating to `encode_bytes_base`.
It validates that the message has even length ≤ 2¹⁶ × 16, splits it into 2-byte chunks decoded as
big-endian GF(2¹⁶) elements, and distributes them round-robin across 16 `Point` value arrays.

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std

namespace spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder.encode_bytes`**
(nat-level):

For an even-length message bounded by `2^16 * 16` bytes, `encode_bytes` returns an encoder with
`idx = 0` in the `Points` state whose GF(2¹⁶) entries match big-endian–decoded byte pairs.
Follows directly from `encode_bytes_base_spec`. -/
@[step]
theorem encode_bytes_spec
    (msg : Slice U8)
    (h_even : msg.length % 2 = 0)
    (h_len : msg.length ≤ 2 ^ 16 * 16) :
    encode_bytes msg ⦃ (result : core.result.Result PolyEncoder encoding.EncodingError) =>
      match result with
      | core.result.Result.Ok ⟨idx, EncoderState.Points pts⟩ =>
        idx = 0#u32 ∧
        (∀ (j : Nat), j < 16 →
          ∀ g ∈ pts[j]!.value.val,
            ∃ (c : Slice U8),
              c.length = 2 ∧
              g.toGF216 = (256 * c[0]! + c[1]!).toGF216)
      | _ => False ⦄ := by
  unfold encode_bytes
  step*
  exact result_post

end spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder
