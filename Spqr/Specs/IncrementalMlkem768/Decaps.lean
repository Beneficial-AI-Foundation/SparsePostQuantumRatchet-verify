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

All steps except (4) are total once the length preconditions hold: the three slice→array
conversions succeed exactly because the input lengths match the target array sizes, and the
final `to_vec` is total for `u8` (whose `Clone` is the identity). Step (4) calls an opaque
axiom (`decapsulate_compressed_key`) that returns a `Result`; since its body is not modelled we
cannot prove it never fails, so the specification is stated under the hypothesis that the
underlying KEM decapsulation succeeds. Under that hypothesis the result is the `to_vec` of a
`[u8; 32]` array and therefore has length exactly 32, matching the Rust `ensures`.

**Source**: src/incremental_mlkem768.rs (lines 156:0-169:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

/-- **Spec and proof concerning `incremental_mlkem768.decaps`**:

Under the length preconditions on `dk`, `ct1`, `ct2`, and assuming the opaque library
decapsulation `decapsulate_compressed_key` succeeds on the converted inputs, `decaps` succeeds
and returns a 32-byte shared secret:
  `result.length = 32`. -/
theorem decaps_spec
    (dk ct1 ct2 : alloc.vec.Vec Std.U8)
    (h_dk : dk.length = 2400) (h_ct1 : ct1.length = 960) (h_ct2 : ct2.length = 128)
    (h_dec : ∀ (k : Array Std.U8 2400#usize)
               (c1 : libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1 960#usize)
               (c2 : libcrux_ml_kem.ind_cca.incremental.types.Ciphertext2 128#usize),
      ∃ ss, libcrux_ml_kem.mlkem768.incremental.decapsulate_compressed_key k c1 c2 = ok ss) :
    decaps dk ct1 ct2 ⦃ result => result.length = 32 ⦄ := by
  unfold decaps
  -- Step through `as_slice ct1` and `try_from 960`.
  step*
  -- `r` is the result of converting `ct1` into a `[u8; 960]`; it is `Ok` because
  -- `s.length = ct1.length = 960`.
  have hs : s.length = 960 := by simp only [Slice.length, s_post]; exact h_ct1
  rcases r with a | err
  swap
  · simp only [hs, ne_eq, not_true_eq_false] at r_post
  -- `expect (Ok a) = ok a`; then step through `ct2`'s `as_slice` and `try_from 128`.
  simp only [core.result.Result.expect]
  step*
  have hs1 : s1.length = 128 := by simp only [Slice.length, s1_post]; exact h_ct2
  rcases r1 with a1 | err1
  swap
  · simp only [hs1, ne_eq, not_true_eq_false] at r1_post
  -- `ct2` converted (`expect (Ok a1)` reduces by iota); step through `dk`'s `as_slice`.
  dsimp only
  step*
  -- `dk`'s conversion uses `TryFromSharedArraySlice.try_from`, which has no step spec.
  have hs2 : s2.len = 2400#usize := by
    have h : s2.length = 2400 := by simp only [Slice.length, s2_post]; exact h_dk
    have := Slice.len_val s2
    scalar_tac
  simp only [core.array.TryFromSharedArraySlice.try_from, hs2, dif_pos]
  step*
  -- Now the opaque library decapsulation: use the success hypothesis. The result is a
  -- `[u8; 32]` array, which is re-sliced and `to_vec`-ed into a length-32 `Vec`.
  obtain ⟨ss, hss⟩ := h_dec ⟨s2.val, by scalar_tac⟩ { value := a } { value := a1 }
  rw [hss]
  -- Re-slice the `[u8; 32]` array and `to_vec` it: the result has length 32.
  step*

end spqr.incremental_mlkem768
