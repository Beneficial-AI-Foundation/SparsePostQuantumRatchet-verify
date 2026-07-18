/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Authenticator.MACSIZE
import Spqr.Auxiliary.Aeneas.Slice
import Spqr.Auxiliary.Aeneas.Vec
import Spqr.Auxiliary.Aeneas.Array
import Spqr.Auxiliary.Aeneas.ArraySlice
import Spqr.Auxiliary.Aeneas.SpecRefl
import Spqr.Specs.Aeneas.SliceConcat

/-!
# Spec theorem for `spqr::authenticator::Authenticator::mac_hdr`

`mac_hdr` produces an authentication tag that lets the receiver verify a
header came from the legitimate sender and was not altered.

The tag is computed by feeding three concatenated inputs into HMAC-SHA256 under
a shared secret key:

1. A fixed 33-byte label MAC_HDR_LABEL identifying the tag's purpose
  (preventing confusion with tags used elsewhere in the protocol).
2. The current epoch counter, big-endian encoded as 8 bytes.
3. The header itself.

The output is a 32-byte tag.

**Source:** "spqr/src/authenticator.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace spqr.authenticator.Authenticator

/-- The 33-byte domain-separation label `"Signal_PQCKA_V1_MLKEM768:ekheader"`
prefixed to the HMAC input in `mac_hdr`. -/
def MAC_HDR_LABEL : List U8 :=
  [83#u8, 105#u8, 103#u8, 110#u8, 97#u8, 108#u8, 95#u8, 80#u8, 81#u8,
   67#u8, 75#u8, 65#u8, 95#u8, 86#u8, 49#u8, 95#u8, 77#u8, 76#u8, 75#u8,
   69#u8, 77#u8, 55#u8, 54#u8, 56#u8, 58#u8, 101#u8, 107#u8, 104#u8,
   101#u8, 97#u8, 100#u8, 101#u8, 114#u8]

@[simp, grind =]
theorem MAC_HDR_LABEL_length : MAC_HDR_LABEL.length = 33 := by rfl

open List core.num.U64 in
/-- **Spec theorem for `spqr::authenticator::Authenticator::mac_hdr`**
• Given the boundedness hypotheses on `self.mac_key` and `hdr`,
  `mac_hdr self ep hdr` does not panic.
• The returned `Vec U8` has length `MACSIZE` (= 32 bytes).
• The returned `Vec U8` equals the output of `libcrux_hmac.hmac` on key `self.mac_key`
  and data `MAC_HDR_LABEL ++ ep.to_be_bytes ++ hdr`.
-/
@[step]
theorem mac_hdr_spec (self : Authenticator) (ep : U64) (hdr : Slice U8)
    (h_key : self.mac_key.length ≤ U32.max)
    (h_data : hdr.length + 41 ≤ U32.max) :
    mac_hdr self ep hdr ⦃ (result : alloc.vec.Vec U8) =>
      result.length = MACSIZE.val ∧
      let data : Slice U8 := Slice.make (MAC_HDR_LABEL ++ to_be_bytes ep ++ hdr);
      libcrux_hmac.hmac .Sha256 self.mac_key data (some MACSIZE) = ok result ⦄ := by
  unfold mac_hdr MACSIZE
  have := refl_of% libcrux_hmac.hmac_sha256_tag32_spec
  step*
  · simp [*]; grind
  · simp [*]; grind
  · refine ⟨by simp [*], ?_⟩
    convert ‹libcrux_hmac.hmac .Sha256 _ _ _ = ok result›
    · rfl
    · apply Subtype.ext; simp [core.num.U64.to_be_bytes, *, MAC_HDR_LABEL]

end spqr.authenticator.Authenticator
