/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-! # Spec theorem for
`spqr::{impl core::cmp::PartialEq<spqr::SecretOutput> for spqr::SecretOutput}::eq`

Structural equality for `SecretOutput`: same variant and equal inner `Vec<u8>` payloads.
Compares discriminants first; delegates to `PartialEqVec.eq` for `Send`/`Recv` payloads.

**Source**: spqr/src/lib.rs -/

open Aeneas Aeneas.Std Result

namespace spqr.SecretOutput.Insts.CoreCmpPartialEqSecretOutput

/-- `List.allM` with `PartialEqU8.eq` on zipped lists decides list equality. -/
private lemma allM_zip_u8_post
    (xs ys : List Std.U8) (h_len : xs.length = ys.length) :
    ∃ b : Bool,
      List.allM (fun (p : Std.U8 × Std.U8) =>
        core.cmp.PartialEqU8.eq p.1 p.2) (List.zip xs ys) = ok b ∧
      (b = true ↔ xs = ys) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨true, rfl, by simp⟩
    | cons _ _ => simp at h_len
  | cons x xs ih =>
    cases ys with
    | nil => simp at h_len
    | cons y ys =>
      have h_len' : xs.length = ys.length := by
        simpa [List.length_cons] using h_len
      obtain ⟨b_tail, hb_tail_eq, hb_tail_iff⟩ := ih ys h_len'
      change ∃ b, List.allM _ ((x, y) :: List.zip xs ys) = ok b ∧ _
      simp only [List.allM, liftFun2, bind_tc_ok, core.cmp.impls.PartialEqU8.eq]
      by_cases hxy : x = y
      · subst hxy
        simp only
        exact ⟨b_tail, hb_tail_eq, by
          rw [hb_tail_iff]
          constructor
          · intro h; rw [h]
          · intro h; exact (List.cons.inj h).2⟩
      · simp only [decide_eq_false hxy]
        exact ⟨false, rfl, by
          simp only [Bool.false_eq_true, false_iff]
          intro h; exact hxy (List.cons.inj h).1⟩

/-- `PartialEqVec.eq` on `Vec<u8>` is propositional equality. -/
@[step]
private theorem eq_vec_u8_spec
    (v1 v2 : alloc.vec.Vec Std.U8) :
    alloc.vec.partial_eq.PartialEqVec.eq core.cmp.PartialEqU8 v1 v2
      ⦃ (r : Bool) => r = true ↔ v1 = v2 ⦄ := by
  simp only [alloc.vec.partial_eq.PartialEqVec.eq]
  split
  · rename_i h_len
    obtain ⟨b, hb_eq, hb_iff⟩ := allM_zip_u8_post v1.val v2.val h_len
    apply WP.exists_imp_spec
    exact ⟨b, hb_eq, by
      rw [hb_iff]
      constructor
      · intro h; cases v1; cases v2; simp_all
      · intro h; subst h; rfl⟩
  · grind
/--
**Spec theorem for `spqr.SecretOutput.Insts.CoreCmpPartialEqSecretOutput.eq`**:

Structural equality on two `SecretOutput` values: `true` iff same variant with equal payloads,
`false` on variant mismatch. Always succeeds (no panic). Proved by case-splitting and `step*`.

**Source**: spqr/src/lib.rs (line 73)
-/
@[step]
theorem eq_spec (self other : spqr.SecretOutput) :
    eq self other ⦃ (result : Bool) =>
      (self = .None ∧ other = .None → result = true) ∧
      (∀ a b, self = .Send a ∧  other = .Send b → (result = true ↔ a = b)) ∧
      (∀ a b, self = .Recv a ∧ other = .Recv b → (result = true ↔ a = b)) ∧
      ((self = .None ∧ (∃ s, other = .Send s ∨ other = .Recv s)) ∨
       ((∃ s, self = .Send s ∨ self = .Recv s) ∧ other = .None) ∨
       ((∃ s, self = .Send s) ∧ (∃ s, other = .Recv s)) ∨
       ((∃ s, self = .Recv s) ∧ (∃ s, other = .Send s)) →
       result = false) ⦄ := by
  unfold eq
  match self, other with
  | .None, .None =>
    simp only [read_discriminant, SecretOutput.read_discriminant]; step*; simp_all
  | .None, .Send _ =>
    simp only [read_discriminant, SecretOutput.read_discriminant]; step*; simp_all
  | .None, .Recv _ =>
    simp only [read_discriminant, SecretOutput.read_discriminant]; step*; simp_all
  | .Send _, .None =>
    simp only [read_discriminant, SecretOutput.read_discriminant]; step*; simp_all
  | .Send a, .Send b =>
    simp only [read_discriminant, SecretOutput.read_discriminant]; step*; simp_all
  | .Send _, .Recv _ =>
    simp only [read_discriminant, SecretOutput.read_discriminant]; step*; simp_all
  | .Recv _, .None =>
    simp only [read_discriminant, SecretOutput.read_discriminant]; step*; simp_all
  | .Recv _, .Send _ =>
    simp only [read_discriminant, SecretOutput.read_discriminant]; step*; simp_all
  | .Recv a, .Recv b =>
    simp only [read_discriminant, SecretOutput.read_discriminant]; step*; simp_all

end spqr.SecretOutput.Insts.CoreCmpPartialEqSecretOutput
