/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Authenticator.MACSIZE
import Spqr.Specs.Kdf.Hkdf
import Spqr.Specs.Kdf.HkdfToVec
import Spqr.Auxiliary.Aeneas.Slice
import Spqr.Auxiliary.Aeneas.Vec
import Spqr.Auxiliary.Aeneas.Array
import Spqr.Auxiliary.Aeneas.ArraySlice
import Spqr.Specs.Aeneas.SliceConcat

/-! # Spec theorem for `spqr::authenticator::Authenticator::update`

Source: "spqr/src/authenticator.rs" -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace spqr.authenticator.Authenticator

/-- The 45-byte domain-separation label used as the HKDF info prefix in `update`. -/
def UpdateLabel : List U8 :=
  [83#u8, 105#u8, 103#u8, 110#u8, 97#u8, 108#u8, 95#u8, 80#u8, 81#u8,
   67#u8, 75#u8, 65#u8, 95#u8, 86#u8, 49#u8, 95#u8, 77#u8, 76#u8, 75#u8,
   69#u8, 77#u8, 55#u8, 54#u8, 56#u8, 58#u8, 65#u8, 117#u8, 116#u8,
   104#u8, 101#u8, 110#u8, 116#u8, 105#u8, 99#u8, 97#u8, 116#u8, 111#u8,
   114#u8, 32#u8, 85#u8, 112#u8, 100#u8, 97#u8, 116#u8, 101#u8]

@[simp, grind =]
theorem UpdateLabel_length : UpdateLabel.length = 45 := by rfl

open List core.num.U64 in
/-- Spec theorem for `spqr::authenticator::Authenticator::update`. Requires that the current root
key concatenated with `k` fits in memory. The two new keys are the halves of a 64-octet
HKDF-SHA256 output, salted with 32 zero bytes and keyed on `self.root_key ++ k`. -/
@[step]
theorem update_spec (self : Authenticator) (ep : U64) (k : Slice U8)
    (h : self.root_key.length + k.length ≤ Usize.max) :
    update self ep k ⦃ (result : Authenticator) =>
      result.root_key.length = 32 ∧ result.mac_key.length = 32 ∧
      result.root_key.val ++ result.mac_key.val
        = hkdf (replicate 32 0#u8) (self.root_key.val ++ k.val)
          (UpdateLabel ++ to_be_bytes ep) 64 ⦄ := by
  unfold update
  step*
  · simp [*]
  · simp [*]; grind
  · simp_all [UpdateLabel]

end spqr.authenticator.Authenticator
