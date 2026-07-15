/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Authenticator.MACSIZE

/-!
# Spec theorem for `spqr::authenticator::Authenticator::mac_ct`

`mac_ct` produces an authentication tag that lets the receiver verify a
ciphertext came from the legitimate sender and was not altered.

The tag is computed by feeding three concatenated inputs into HMAC-SHA256 under
a shared secret key:

1. A fixed 35-byte label MAC_CT_LABEL identifying the tag's purpose
  (preventing confusion with tags used elsewhere in the protocol).
2. The current epoch counter, big-endian encoded as 8 bytes.
3. The ciphertext itself.

The output is a 32-byte tag.

**Source:** "spqr/src/authenticator.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace spqr.authenticator.Authenticator

/-- The 35-byte domain-separation label `"Signal_PQCKA_V1_MLKEM768:ciphertext"`
prefixed to the HMAC input in `mac_ct`. -/
def MAC_CT_LABEL : List U8 :=
  [83#u8, 105#u8, 103#u8, 110#u8, 97#u8, 108#u8, 95#u8, 80#u8, 81#u8,
   67#u8, 75#u8, 65#u8, 95#u8, 86#u8, 49#u8, 95#u8, 77#u8, 76#u8, 75#u8,
   69#u8, 77#u8, 55#u8, 54#u8, 56#u8, 58#u8, 99#u8, 105#u8, 112#u8,
   104#u8, 101#u8, 114#u8, 116#u8, 101#u8, 120#u8, 116#u8]

@[simp, grind =]
theorem MAC_CT_LABEL_length : MAC_CT_LABEL.length = 35 := by rfl

/-- **Step spec for `core::array::[T; N]::as_slice`** (TODO: relocate). -/
@[step]
theorem _root_.core.array.Array.as_slice_spec {T : Type} {N : Usize} (a : Array T N) :
    core.array.Array.as_slice a ⦃ (s : Slice T) => s.val = a.val ⦄ := by
  simp [core.array.Array.as_slice, WP.spec_ok]

/-- TODO: relocate -/
@[step]
theorem _root_.alloc.slice.Slice.concat_shared_id_spec {T : Type}
    (cloneInst : core.clone.Clone T) (hclone : ∀ x, cloneInst.clone x = ok x)
    (sv : Slice (Slice T))
    (hlen : (sv.val.map (·.val)).flatten.length ≤ Usize.max) :
    alloc.slice.Slice.concat
        (Slice.Insts.AllocSliceConcatTVec cloneInst
          { borrow := Shared0T.Insts.CoreBorrowBorrow.borrow }) sv
      ⦃ (v : alloc.vec.Vec T) => v.val = (sv.val.map (·.val)).flatten ⦄ := by
  simp only [alloc.slice.Slice.concat_eq]
  exact Slice.Insts.AllocSliceConcatTVec.concat_shared_id_spec cloneInst hclone sv hlen


-- TODO: upstream to Aeneas
def _root_.Aeneas.Std.Slice.make {α : Type} (l : List α) (h : l.length ≤ Usize.max := by grind) :
  Slice α := ⟨l, h⟩

@[simp] theorem _root_.Aeneas.Std.Slice.val_make {α : Type} (l : List α) (h) :
    (Slice.make l h).val = l := rfl

@[simp] theorem _root_.Aeneas.Std.Slice.length_make {α : Type} (l : List α) (h) :
    (Slice.make l h).length = l.length := rfl

@[simp] theorem _root_.Aeneas.Std.Slice.make_val {α : Type} (s : Slice α) (h) :
    Slice.make s.val h = s := rfl

theorem _root_.Aeneas.Std.Slice.make_inj {α : Type} (l₁ l₂ : List α) (h₁ h₂) :
    Slice.make l₁ h₁ = Slice.make l₂ h₂ ↔ l₁ = l₂ :=
  Subtype.ext_iff

/-- Strengthen any spec's postcondition with the *call identity* `m = ok r`. TODO: relocate -/
theorem spec_refl {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) :
    m ⦃ fun r => P r ∧ m = ok r ⦄ := by
  obtain ⟨r, h_eq, h_post⟩ := spec_imp_exists h
  exact exists_imp_spec ⟨r, h_eq, h_post, h_eq⟩

open List core.num.U64 in
/-- **Spec theorem for `spqr::authenticator::Authenticator::mac_ct`**
• Given the boundedness hypotheses on `self.mac_key` and `ct`, `mac_ct self ep ct` does not panic.
• The returned `Vec U8` has length `MACSIZE` (= 32 bytes).
• The returned `Vec U8` equals the output of `libcrux_hmac.hmac` on key `self.mac_key`
  and data `MAC_CT_LABEL ++ ep.to_be_bytes ++ ct`. -/
@[step]
theorem mac_ct_spec (self : Authenticator) (ep : U64) (ct : Slice U8)
    (h_key : self.mac_key.length ≤ U32.max) (h_data : ct.length + 43 ≤ U32.max) :
    mac_ct self ep ct ⦃ (result : alloc.vec.Vec U8) =>
      result.length = MACSIZE.val ∧
      let data : Slice U8 := Slice.make (MAC_CT_LABEL ++ to_be_bytes ep ++ ct);
      libcrux_hmac.hmac .Sha256 self.mac_key data (some MACSIZE) = ok result ⦄ := by
  unfold mac_ct
  simp only [MACSIZE]
  have hmac_refl := fun k d hk hd => spec_refl (libcrux_hmac.hmac_sha256_tag32_spec k d hk hd)
  step*
  · simp [*, Array.make]; grind
  · exact h_key
  · simp [*, Array.make, alloc.vec.Vec.deref, Slice.length]; grind
  · refine ⟨by simp [*], ?_⟩
    convert result_post2 using 2
    · rfl
    · apply Subtype.ext
      simp [core.num.U64.to_be_bytes, alloc.vec.Vec.deref, *, MAC_CT_LABEL, Array.make]

end spqr.authenticator.Authenticator
