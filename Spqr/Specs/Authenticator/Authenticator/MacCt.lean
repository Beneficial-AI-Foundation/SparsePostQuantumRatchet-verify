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

/-- TODO: relocate -/
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

-- TODO: upstream to Aeneas (`Vec.deref` carries the same `val`, hence the same `length`).
@[simp] theorem _root_.Aeneas.Std.alloc.vec.Vec.deref_val {α : Type} (v : alloc.vec.Vec α) :
    (alloc.vec.Vec.deref v).val = v.val := rfl

@[simp, scalar_tac_simps] theorem _root_.Aeneas.Std.alloc.vec.Vec.deref_length {α : Type}
    (v : alloc.vec.Vec α) : (alloc.vec.Vec.deref v).length = v.length := rfl

-- TODO: upstream to Aeneas (`Array.make` currently has no `val`/`length` simp lemmas).
@[simp, grind =] theorem _root_.Aeneas.Std.Array.val_make {α : Type}
    (n : Usize) (l : List α) (h) : (Array.make n l h).val = l := rfl

-- TODO: relocate
/-- Strengthen any spec's postcondition with the identity `m = ok r`. -/
theorem spec_refl {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) :
    m ⦃ fun r => P r ∧ m = ok r ⦄ := by
  obtain ⟨r, h_eq, h_post⟩ := spec_imp_exists h
  exact exists_imp_spec ⟨r, h_eq, h_post, h_eq⟩

-- TODO: relocate
open Lean Elab Term Meta in
/-- `refl_of% e` turns a spec theorem `∀ xs, m xs ⦃ P xs ⦄` into its reflexive strengthening
`∀ xs, m xs ⦃ fun r => P xs r ∧ m xs = ok r ⦄`, telescoping the binders and applying `spec_refl`
under them. Any arity (including none). Errors if `e` is not, after telescoping, a spec. -/
elab "refl_of% " t:term : term => withRef t do
  let e ← elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars (← inferType e)
  forallTelescope ty fun xs body => do
    let refled ←
      try mkAppM ``spec_refl #[mkAppN e xs]
      catch _ =>
        throwError "refl_of%: expected a spec `m ⦃ P ⦄`, but the statement concludes \
          with{indentExpr body}"
    mkLambdaFVars xs refled

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
  unfold mac_ct MACSIZE
  have := refl_of% libcrux_hmac.hmac_sha256_tag32_spec
  step*
  · simp [*]; grind
  · simp [*]; grind
  · refine ⟨by simp [*], ?_⟩
    have : (Slice.make (MAC_CT_LABEL ++ to_be_bytes ep ++ ct) : Slice U8) = ct_mac_data.deref :=
      Subtype.ext (by simp [core.num.U64.to_be_bytes, *, MAC_CT_LABEL])
    rwa [this]

end spqr.authenticator.Authenticator
