/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Authenticator.MACSIZE
import Spqr.Specs.Kdf.HkdfToVec
import Spqr.Auxiliary.Aeneas.Slice
import Spqr.Auxiliary.Aeneas.Vec
import Spqr.Auxiliary.Aeneas.Array
import Spqr.Auxiliary.Aeneas.ArraySlice
import Spqr.Auxiliary.Aeneas.SpecRefl
import Spqr.Specs.Aeneas.SliceConcat
import Spqr.Specs.Kdf.HkdfToVec

/-!
# Spec theorem for `spqr::authenticator::Authenticator::update`

`update` ratchets the authenticator's key material by running HKDF-SHA256 with:

- **Salt**: 32 zero bytes.
- **IKM**: the current `root_key` concatenated with the caller-supplied key `k`.
- **Info**: the 45-byte domain label `UPDATE_LABEL` followed by the epoch encoded as 8 big-endian bytes.

The 64-byte HKDF output is split: the first 32 bytes become the new `root_key` and the last
32 become the new `mac_key`.

**Source:** "spqr/src/authenticator.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace spqr.authenticator.Authenticator

/-- The 45-byte domain-separation label `"Signal_PQCKA_V1_MLKEM768:Authenticator Update"`
used as the HKDF info prefix in `update`. -/
def UPDATE_LABEL : List U8 :=
  [83#u8, 105#u8, 103#u8, 110#u8, 97#u8, 108#u8, 95#u8, 80#u8, 81#u8,
   67#u8, 75#u8, 65#u8, 95#u8, 86#u8, 49#u8, 95#u8, 77#u8, 76#u8, 75#u8,
   69#u8, 77#u8, 55#u8, 54#u8, 56#u8, 58#u8, 65#u8, 117#u8, 116#u8,
   104#u8, 101#u8, 110#u8, 116#u8, 105#u8, 99#u8, 97#u8, 116#u8, 111#u8,
   114#u8, 32#u8, 85#u8, 112#u8, 100#u8, 97#u8, 116#u8, 101#u8]

@[simp, grind =]
theorem UPDATE_LABEL_length : UPDATE_LABEL.length = 45 := by rfl

open List core.num.U64 in
/-- **Spec theorem for `spqr::authenticator::Authenticator::update`**
• Given `self.root_key.length + k.length ≤ Usize.max`, the call does not panic.
• The returned authenticator's keys are the first and second 32 bytes of a 64-byte HKDF output
  keyed on the concatenation of the current root key and `k`.
-/
@[step]
theorem update_spec (self : Authenticator) (ep : U64) (k : Slice U8)
    (h : self.root_key.length + k.length ≤ Usize.max) :
    update self ep k ⦃ (result : Authenticator) =>
      result.root_key.length = 32 ∧
      result.mac_key.length = 32 ∧
      Subtype.val <$> kdf.hkdf_to_vec
          (Slice.make (List.replicate 32 0#u8))
          (Slice.make (self.root_key.val ++ k.val))
          (Slice.make (UPDATE_LABEL ++ to_be_bytes ep))
          64#usize
        = ok (result.root_key.val ++ result.mac_key.val) ⦄ := by
  unfold update
  have hkdf := refl_of% spqr.kdf.hkdf_to_vec_spec
  step*
  sorry

end spqr.authenticator.Authenticator
