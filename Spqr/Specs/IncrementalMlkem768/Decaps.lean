/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Zhang Liao
-/
import SrcTranslated.Funs
import SrcTranslated.FunsExternal

/-! # Spec Theorem for `spqr::incremental_mlkem768::decaps`

Specification and proof for `incremental_mlkem768.decaps`, which decapsulates an
ML-KEM-768 ciphertext (split into `ct1` and `ct2`) under a decapsulation key `dk` to
recover the 32-byte shared secret.

The extracted Lean body does the following:
  1. View `ct1` as a slice and convert it into a fixed-size `[u8; 960]` array (`try_into`),
     `expect`-ing the conversion to succeed.
  2. View `ct2` as a slice and convert it into a fixed-size `[u8; 128]` array.
  3. View `dk` as a slice and convert it into a fixed-size `[u8; 2400]` array.
  4. Call the (opaque, library-provided) `incremental::decapsulate_compressed_key`, which
     returns the shared secret as a `[u8; 32]` array.
  5. Re-view that array as a slice and `to_vec` it into the returned `Vec<u8>`.

The Rust contract (`hax_lib`) is:
  `requires ct1.len() == 960 && ct2.len() == 128 && dk.len() == 2400`
  `ensures  |result| result.len() == 32`

The specification is *functional*: `decaps` is a thin wrapper, so its output is pinned to
the output of the underlying (opaque) library decapsulation.  The hypothesis `h_dec`
supplies the behaviour of `decapsulate_compressed_key` on the fixed-size images `dkA`,
`c1`, `c2` of the three input vectors (identified by the value equalities `h_dkA`,
`h_c1`, `h_c2`); the conclusion states that `decaps` succeeds and returns exactly the
bytes of that shared secret.  The Rust `ensures` (`result.len() == 32`) is the second
conjunct.  Stating `h_dec` as an `ok`-equation on the *caller-provided* array objects
(rather than on arrays rebuilt inside the spec) lets a caller discharge it directly
from a specification axiom such as `decapsulate_compressed_key_roundtrip`
(`Spqr/Specs/LibcruxMlKem/Incremental/DecapsulateCompressedKey.lean`), which is how
the round-trip proof (`Spqr/Specs/IncrementalMlkem768/Roundtrip.lean`) consumes this
theorem.  The length preconditions of the Rust contract are implied by the value
equalities (the arrays have fixed sizes) and are derived in the proof.

All steps except (4) are total once the length preconditions hold: the three slice→array
conversions succeed exactly because the input lengths match the target array sizes, and the
final `to_vec` is total for `u8` (whose `Clone` is the identity).

**Source**: src/incremental_mlkem768.rs (lines 156:0-169:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

open libcrux_ml_kem.ind_cca.incremental.types (Ciphertext1 Ciphertext2)

/-- **Spec and proof concerning `incremental_mlkem768.decaps`**:

Let `dkA`, `c1`, `c2` be the fixed-size images of the input vectors `dk`, `ct1`, `ct2`
(hypotheses `h_dkA`, `h_c1`, `h_c2`), and assume the opaque library decapsulation
returns `ss` on them (`h_dec`).  Then `decaps` succeeds and returns exactly the bytes
of `ss`: `result.val = ss.val`, and in particular the 32-byte length of the Rust
`ensures`: `result.length = 32`. -/
theorem decaps_spec
    (dk ct1 ct2 : alloc.vec.Vec Std.U8)
    (dkA : Array Std.U8 2400#usize)
    (c1 : Ciphertext1 960#usize) (c2 : Ciphertext2 128#usize)
    (ss : Array Std.U8 32#usize)
    (h_dkA : dkA.val = dk.val) (h_c1 : c1.value.val = ct1.val) (h_c2 : c2.value.val = ct2.val)
    (h_dec : libcrux_ml_kem.mlkem768.incremental.decapsulate_compressed_key dkA c1 c2 = ok ss) :
    decaps dk ct1 ct2 ⦃ result => result.val = ss.val ∧ result.length = 32 ⦄ := by
  sorry
  -- -- The length preconditions of the Rust contract follow from the value equalities,
  -- -- since `dkA`, `c1`, `c2` have fixed sizes.
  -- have h_dk_len : dk.length = 2400 := by have := congrArg List.length h_dkA; scalar_tac
  -- have h_ct1_len : ct1.length = 960 := by have := congrArg List.length h_c1; scalar_tac
  -- have h_ct2_len : ct2.length = 128 := by have := congrArg List.length h_c2; scalar_tac
  -- unfold decaps
  -- -- Step through `as_slice ct1` and `try_from 960`.
  -- step*
  -- -- `r` is the result of converting `ct1` into a `[u8; 960]`; it is `Ok` because
  -- -- `s.length = ct1.length = 960`.
  -- have hs : s.length = 960 := by simp only [Slice.length, s_post]; exact h_ct1_len
  -- rcases r with a | err
  -- swap
  -- · simp only [hs, ne_eq, not_true_eq_false] at r_post
  -- simp only at r_post
  -- obtain ⟨ha_val, ha_len⟩ := r_post
  -- -- `expect (Ok a) = ok a`; then step through `ct2`'s `as_slice` and `try_from 128`.
  -- simp only [core.result.Result.expect]
  -- step*
  -- have hs1 : s1.length = 128 := by simp only [Slice.length, s1_post]; exact h_ct2_len
  -- rcases r1 with a1 | err1
  -- swap
  -- · simp only [hs1, ne_eq, not_true_eq_false] at r1_post
  -- simp only at r1_post
  -- obtain ⟨ha1_val, ha1_len⟩ := r1_post
  -- -- `ct2` converted (`expect (Ok a1)` reduces by iota); step through `dk`'s `as_slice`.
  -- dsimp only
  -- step*
  -- -- `dk`'s conversion uses `TryFromSharedArraySlice.try_from`, which has no step spec.
  -- have hs2 : s2.len = 2400#usize := by
  --   have h : s2.length = 2400 := by simp only [Slice.length, s2_post]; exact h_dk_len
  --   have := Slice.len_val s2
  --   scalar_tac
  -- simp only [core.array.TryFromSharedArraySlice.try_from, hs2, dif_pos]
  -- step*
  -- -- The rebuilt array and ciphertexts are exactly the caller-provided `dkA`, `c1`, `c2`.
  -- have h_arr : (⟨s2.val, by scalar_tac⟩ : Array Std.U8 2400#usize) = dkA :=
  --   Subtype.ext (s2_post.trans h_dkA.symm)
  -- have h_c1' : ({ value := a } : Ciphertext1 960#usize) = c1 := by
  --   have h : a = c1.value := Subtype.ext ((ha_val.trans s_post).trans h_c1.symm)
  --   rw [h]
  -- have h_c2' : ({ value := a1 } : Ciphertext2 128#usize) = c2 := by
  --   have h : a1 = c2.value := Subtype.ext ((ha1_val.trans s1_post).trans h_c2.symm)
  --   rw [h]
  -- rw [h_arr, h_c1', h_c2', h_dec]
  -- -- Re-slice the returned `[u8; 32]` array and `to_vec` it: the result carries the
  -- -- bytes of `ss` and hence has length 32.
  -- simp only [step_simps]
  -- step as ⟨res, h_res⟩
  -- step as ⟨resV, h_resV⟩
  -- rw [← h_resV, h_res]
  -- simp

end spqr.incremental_mlkem768
