/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.Conversion.Compress
/-!
# FIPS 203 Algorithm 12: `Decompress_d`

NIST FIPS 203 (ML-KEM, August 2024), § 4.2.1, defines the decompression map

  `Decompress_d : ℤ_{2^d} → ℤ_q`

which is the approximate inverse of `Compress_d`.  Given a compressed value
`y ∈ {0, …, 2^d − 1}`, it recovers an element of `ℤ_q` via

```
Decompress_d(y):                          ▷ y ∈ {0, …, 2^d − 1}
  return ⌈(q / 2^d) · y⌋
```

Concretely: `(q · y + 2^{d−1}) >>> d`, i.e. multiply by `q`, add a half-`2^d`
bias for rounding, then right-shift by `d` bits.

**Source**: NIST FIPS 203, § 4.2.1, Algorithm 12
-/

@[expose] public section

noncomputable section

namespace Fips203

/-! ## Coefficient-level decompression (Algorithm 12) -/

/-- **Spec theorem for `Fips203.decompress`** (Algorithm 12):

• Takes a compression depth `d` and a compressed value `y ∈ ℤ_{2^d}`.
• Computes `⌈(q / 2^d) · y⌋` as `(q · y + 2^{d−1}) >>> d`.
• Returns the result as an element of `ℤ_q` via `Zq.ofNat`.

**Source**: NIST FIPS 203, § 4.2.1, Algorithm 12
-/
theorem decompress_spec (d : ℕ) (y : ℕ) :
    decompress d y = Zq.ofNat (((q * y) + (1 <<< (d - 1))) >>> d) := rfl

/-- Decompressing zero yields zero in `ℤ_q` (for `d ≥ 1`). -/
theorem decompress_zero' (d : ℕ) (hd : 1 ≤ d) : decompress d 0 = (0 : Zq) :=
  decompress_zero d hd

/-- The `val` of `decompress d y` is strictly less than `q`. -/
theorem decompress_val_lt_q (d : ℕ) (y : ℕ) :
    (decompress d y).val < q := ZMod.val_lt _

/-- `Decompress_d` is (weakly) monotone at the pre-reduction level. -/
theorem decompress_nat_mono (d : ℕ) (y₁ y₂ : ℕ) (h : y₁ ≤ y₂) :
    ((q * y₁ + (1 <<< (d - 1))) >>> d) ≤
    ((q * y₂ + (1 <<< (d - 1))) >>> d) := by
  simp only [Nat.shiftRight_eq_div_pow]
  apply Nat.div_le_div_right
  grind

/-! ## Polynomial-level decompression -/

/-- **Spec theorem for `Fips203.decompressPoly`**:
applies `Decompress_d` coefficient-wise. -/
theorem decompressPoly_spec (d : ℕ) (g : Fin n → ℕ) (i : Fin n) :
    decompressPoly d g i = decompress d (g i) := rfl

/-- Decompressing the zero compressed polynomial yields the zero polynomial. -/
theorem decompressPoly_zero' (d : ℕ) (hd : 1 ≤ d) :
    decompressPoly d (fun _ => 0) = fun _ => (0 : Zq) :=
  decompressPoly_zero d hd

/-- Every coefficient of a decompressed polynomial has `val < q`. -/
theorem decompressPoly_val_lt_q (d : ℕ) (g : Fin n → ℕ) (i : Fin n) :
    (decompressPoly d g i).val < q :=
  decompress_val_lt_q d (g i)

/-! ## Vector-level decompression -/

/-- **Spec theorem for `Fips203.decompressVec`**:
applies `decompressPoly` to each component of the vector. -/
theorem decompressVec_spec (p : ParamSet) (d : ℕ)
    (g : Fin p.k → (Fin n → ℕ)) (j : Fin p.k) :
    decompressVec p d g j = Rq.ofCoeffs (decompressPoly d (g j)) := rfl

/-! ## ML-KEM-768 instantiations -/

/-- Decompress a polynomial with depth `d_u = 10`. -/
theorem decompressPolyDu_spec (g : Fin n → ℕ) :
    decompressPolyDu g = decompressPoly mlkem768.compressionU g := rfl

/-- Decompress a polynomial with depth `d_v = 4`. -/
theorem decompressPolyDv_spec (g : Fin n → ℕ) :
    decompressPolyDv g = decompressPoly mlkem768.compressionV g := rfl

/-- Decompress a vector with depth `d_u = 10` for ML-KEM-768. -/
theorem decompressVecDu_spec (g : Fin mlkem768.k → (Fin n → ℕ)) :
    decompressVecDu g = decompressVec mlkem768 mlkem768.compressionU g := rfl

/-! ## Round-trip error bound (decompression side) -/

/-- The round-trip error `|Decompress_d(Compress_d(x)) − x|_q` is at most
`compressError d = ⌈q / 2^{d+1}⌉`. -/
theorem decompress_compress_error' (d : ℕ) (x : Zq) :
    let y := compress d x
    let x' := decompress d y
    min ((x'.val + q - x.val) % q) ((x.val + q - x'.val) % q) ≤
      compressError d := by
  intro y x'
  have hv : x.val < q := ZMod.val_lt x
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- `d = 0`: `compress 0 x = 0`, `decompress 0 0 = 1`, `compressError 0 = 1665`.
    simp only [y, x', compress, decompress, compressError, Zq.ofNat, ZMod.val_natCast]
    simp only [q] at hv ⊢
    omega
  · obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    -- Write `2^(e+1) = 2 * M` with `M = 2^e ≥ 1`.
    set M := 2 ^ e with hM
    have hMpos : 0 < M := by positivity
    have hN : 2 ^ (e + 1) = 2 * M := by rw [pow_succ]; ring
    have hN2 : 2 ^ (e + 1 + 1) = 4 * M := by rw [pow_succ, pow_succ]; ring
    simp only [y, x', compress, decompress, compressError, Zq.ofNat, Nat.add_sub_cancel,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, one_mul, hN, hN2, ZMod.val_natCast]
    set v := x.val with hv_def
    set y₀ := (2 * M * v + q / 2) / q with hy₀
    set E := (q + 4 * M - 1) / (4 * M) with hE
    -- Division facts for `y₀`.
    have h1 : q * y₀ ≤ 2 * M * v + q / 2 := Nat.mul_div_le _ _
    have h1' : 2 * M * v + q / 2 < q * y₀ + q := by
      have := Nat.lt_div_mul_add (a := 2 * M * v + q / 2) (b := q) (by simp [q])
      rw [hy₀]; linarith [Nat.mul_comm q ((2 * M * v + q / 2) / q)]
    -- `4 * M * E ≥ q`.
    have hE' : q ≤ 4 * M * E := by
      have := Nat.lt_div_mul_add (a := q + 4 * M - 1) (b := 4 * M) (by omega)
      rw [hE]; simp only [q] at this ⊢; grind
    -- `y₀ ≤ 2 * M`.
    have hy₀le : y₀ ≤ 2 * M := by
      by_contra hcon
      push Not at hcon
      have := Nat.mul_le_mul_left q hcon
      simp only [q] at h1 this hv ⊢
      nlinarith
    rcases Nat.lt_or_ge y₀ (2 * M) with hlt | hge
    · -- No wrap-around: `y = y₀`.
      rw [Nat.mod_eq_of_lt hlt]
      set z := (q * y₀ + M) / (2 * M) with hz
      have h2 : 2 * M * z ≤ q * y₀ + M := Nat.mul_div_le _ _
      have h2' : q * y₀ + M < 2 * M * z + 2 * M := by
        have := Nat.lt_div_mul_add (a := q * y₀ + M) (b := 2 * M) (by omega)
        rw [hz]; linarith [Nat.mul_comm (2 * M) ((q * y₀ + M) / (2 * M))]
      -- `z < q`.
      have hzq : z < q := by
        by_contra hcon
        push Not at hcon
        have hA : M * (v + 1) ≤ M * z := Nat.mul_le_mul_left M (by simp only [q] at hcon hv; omega)
        have hB : M * q ≤ M * z := Nat.mul_le_mul_left M hcon
        have hC : q * y₀ ≤ q * (2 * M - 1) := Nat.mul_le_mul_left q (by omega)
        have h2M : 2 * M - 1 + 1 = 2 * M := by omega
        simp only [q] at h1 h2 hA hB hC hv ⊢
        nlinarith
      -- `z ≤ v + E`.
      have hup : z ≤ v + E := by
        by_contra hcon
        push Not at hcon
        have hA : M * (v + E + 1) ≤ M * z := Nat.mul_le_mul_left M hcon
        simp only [q] at h1 h2 hA hE' ⊢
        nlinarith
      -- `v ≤ z + E`.
      have hlow : v ≤ z + E := by
        by_contra hcon
        push Not at hcon
        have hA : M * (z + E + 1) ≤ M * v := Nat.mul_le_mul_left M hcon
        simp only [q] at h1' h2' hA hE' ⊢
        nlinarith
      rw [Nat.mod_eq_of_lt hzq]
      simp only [q] at hzq hv hup hlow ⊢
      grind
    · -- Wrap-around: `y₀ = 2 * M`, so `y = 0` and `x' = 0`.
      have hy₀eq : y₀ = 2 * M := le_antisymm hy₀le hge
      rw [hy₀eq, Nat.mod_self, Nat.mul_zero, Nat.zero_add,
        Nat.div_eq_of_lt (by omega : M < 2 * M), Nat.zero_mod]
      -- `q - v ≤ E`.
      have hA : q ≤ v + E := by
        by_contra hcon
        push Not at hcon
        have hB : M * (v + E + 1) ≤ M * q := Nat.mul_le_mul_left M hcon
        rw [hy₀eq] at h1
        simp only [q] at h1 hB hE' ⊢
        nlinarith
      simp only [q] at hv hA ⊢
      grind

end Fips203
