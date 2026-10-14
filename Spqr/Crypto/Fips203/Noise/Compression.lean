/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.Conversion.Decompress
public import Spqr.Crypto.Fips203.PKE.RoundTrip
/-!
# Compression Rounding Error in Centred Form (FIPS 203, Algorithms 11–12)

The deterministic round-trip
bound `decompress_compress_error'` of `Conversion/Decompress.lean` is stated as a minimum of two
mod-`q` distances.  The noise accounting of `PKE/RoundTrip.lean`, however, measures every noise
term with the **centred absolute value** `absZq`.  This file bridges the two:

* `val_sub_eq` / `absZq_eq_min` — `(a − b).val` and `absZq` in terms of mod-`q` distances;
* `absZq_decompress_compress` — the round-trip error in centred form:
  `absZq (Decompress_d (Compress_d x) − x) ≤ compressError d = ⌈q / 2^{d+1}⌉`;
* `absZq_compressionNoisePoly` — the same bound for the polynomial-level noise term
  `compressionNoisePoly` of `PKE/RoundTrip.lean`;
* the ML-KEM-768 instantiations: error `≤ 2` for `d_u = 10` and `≤ 105` for `d_v = 4`
  (both far below the decryption threshold `⌊q/4⌋ = 832`).

These give the deterministic contribution of compression to the total noise polynomial; step
8.4 combines them with the CBD tail bounds of `Noise/Moments.lean`.

**Source**: NIST FIPS 203, § 4.2.1 (Algorithms 11–12), § 3.3 (decryption failure)
-/

@[expose] public section

noncomputable section

namespace Fips203

/-! ## Centred absolute value vs. mod-`q` distance -/

/-- `(a − b).val` is the mod-`q` distance `(a.val + q − b.val) % q`. -/
theorem val_sub_eq (a b : Zq) : (a - b).val = (a.val + q - b.val) % q := by
  have hb : b.val ≤ q := le_of_lt (ZMod.val_lt b)
  have h : a - b = ((a.val + q - b.val : ℕ) : Zq) := by
    have h1 : (a.val + q - b.val : ℕ) = a.val + (q - b.val) := by omega
    rw [h1, Nat.cast_add, Nat.cast_sub hb, ZMod.natCast_val, ZMod.cast_id]
    simp only [CharP.cast_eq_zero (ZMod q) q, zero_sub, ZMod.natCast_val, ZMod.cast_id]
    ring
  rw [h, ZMod.val_natCast]

/-- The centred absolute value is the minimum of the two mod-`q` distances:
`absZq (a − b) = min ((a.val + q − b.val) % q) ((b.val + q − a.val) % q)`. -/
theorem absZq_eq_min (a b : Zq) :
    absZq (a - b) = min ((a.val + q - b.val) % q) ((b.val + q - a.val) % q) := by
  have hval := val_sub_eq a b
  have ha : a.val < q := ZMod.val_lt a
  have hb : b.val < q := ZMod.val_lt b
  unfold absZq centredRep
  rw [hval]
  simp only [q] at *
  split <;> omega

/-! ## Round-trip error in centred form -/

/-- **Compression round-trip error, centred form**: for every `x ∈ ℤ_q`,
`absZq (Decompress_d (Compress_d x) − x) ≤ compressError d = ⌈q / 2^{d+1}⌉`. -/
theorem absZq_decompress_compress (d : ℕ) (x : Zq) :
    absZq (decompress d (compress d x) - x) ≤ compressError d := by
  have h := decompress_compress_error' d x
  simp only at h
  rw [absZq_eq_min]
  exact h

/-- Polynomial-level form: every coefficient of `compressionNoisePoly f d` (the rounding noise
of `PKE/RoundTrip.lean`) has centred absolute value at most `compressError d`. -/
theorem absZq_compressionNoisePoly (d : ℕ) (f : Fin n → Zq) (idx : Fin n) :
    absZq (compressionNoisePoly f d idx) ≤ compressError d := by
  unfold compressionNoisePoly compressPoly decompressPoly
  exact absZq_decompress_compress d (f idx)

/-! ## ML-KEM-768 instantiations

For the SPQR parameter set, the per-coefficient rounding error of the ciphertext vector
(`d_u = 10`) is at most `2` and of the ciphertext polynomial (`d_v = 4`) at most `105`.  Both
are far below the decryption threshold `⌊q/4⌋ = 832`, leaving the bulk of the noise budget to
the CBD terms analysed in steps 8.2 / 8.4. -/

/-- Rounding error of the `u` component (`d_u = 10`): at most `2` per coefficient. -/
theorem absZq_compressionNoise_du (f : Fin n → Zq) (idx : Fin n) :
    absZq (compressionNoisePoly f mlkem768.compressionU idx) ≤ 2 := by
  have h := absZq_compressionNoisePoly mlkem768.compressionU f idx
  rw [mlkem768CompressionU] at h ⊢
  rw [compressError_10] at h
  exact h

/-- Rounding error of the `v` component (`d_v = 4`): at most `105` per coefficient. -/
theorem absZq_compressionNoise_dv (f : Fin n → Zq) (idx : Fin n) :
    absZq (compressionNoisePoly f mlkem768.compressionV idx) ≤ 105 := by
  have h := absZq_compressionNoisePoly mlkem768.compressionV f idx
  rw [mlkem768CompressionV] at h ⊢
  rw [compressError_4] at h
  exact h

/-- The combined worst-case rounding error `2 + 105 = 107` is below the decryption threshold
`⌊q/4⌋ = 832`, leaving a budget of `725` for the CBD noise terms. -/
theorem compression_budget : compressError 10 + compressError 4 < q / 4 := by
  rw [compressError_10, compressError_4]
  norm_num [q]

end Fips203
