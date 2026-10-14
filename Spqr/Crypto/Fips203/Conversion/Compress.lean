/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.Params
public import Spqr.Crypto.Fips203.Ring
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
/-!
# FIPS 203 Algorithms 11–12: `Compress_d` and `Decompress_d`

NIST FIPS 203 (ML-KEM, August 2024), § 4.2.1, defines a lossy compression map

  `Compress_d : ℤ_q → ℤ_{2^d}`

and its approximate inverse

  `Decompress_d : ℤ_{2^d} → ℤ_q`

used to reduce ciphertext size.  The pair satisfies a bounded round-trip error:

  `|Decompress_d(Compress_d(x)) − x|_q ≤ ⌈q / 2^{d+1}⌉`

The algorithms:

```
Compress_d(x):                            ▷ x ∈ ℤ_q
  return ⌈(2^d / q) · x⌋ mod 2^d

Decompress_d(y):                          ▷ y ∈ {0, …, 2^d − 1}
  return ⌈(q / 2^d) · y⌋
```

**Source**: NIST FIPS 203, § 4.2.1, Algorithms 11–12
-/

@[expose] public section

noncomputable section

namespace Fips203

/-! ## Coefficient-level compression (Algorithms 11–12) -/

/-- `compress d x` is Algorithm 11: `⌈(2^d / q) · x⌋ mod 2^d`. -/
theorem compress_eq (d : ℕ) (x : Zq) :
    compress d x = ((2 ^ d * x.val + (q / 2)) / q) % (2 ^ d) := rfl

/-- `decompress d y` is Algorithm 12: `⌈(q / 2^d) · y⌋`. -/
theorem decompress_eq (d : ℕ) (y : ℕ) :
    decompress d y = Zq.ofNat (((q * y) + (1 <<< (d - 1))) >>> d) := rfl

/-! ## Range bound -/

/-- The output of `compress d x` is strictly less than `2^d`. -/
theorem compress_lt_two_pow (d : ℕ) (x : Zq) : compress d x < 2 ^ d := by
  unfold compress
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity))

/-- Compressing zero yields zero. -/
theorem compress_zero (d : ℕ) : compress d (0 : Zq) = 0 := by
  simp only [compress, ZMod.val_zero, Nat.mul_zero, Nat.zero_add]
  have : q / 2 / q = 0 := by simp [q]
  simp [this]

/-- Decompressing zero yields zero (for `d ≥ 1`, which holds for all FIPS 203 parameters). -/
theorem decompress_zero (d : ℕ) (hd : 1 ≤ d) : decompress d 0 = (0 : Zq) := by
  simp only [decompress, Nat.mul_zero, Nat.zero_add]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  simp only [Nat.succ_sub_one, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have : 2 ^ d / 2 ^ (d + 1) = 0 :=
    Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  simp [this, Zq.ofNat]

/-! ## Polynomial-level compression -/

/-- Apply `Compress_d` coefficient-wise to a polynomial `f ∈ R_q`, represented as
`Fin n → ℤ_q`.  Returns `Fin n → ℕ` with each output in `{0, …, 2^d − 1}`. -/
def compressPoly (d : ℕ) (f : Fin n → Zq) : Fin n → ℕ :=
  fun i => compress d (f i)

/-- Apply `Decompress_d` coefficient-wise to a compressed polynomial. -/
def decompressPoly (d : ℕ) (g : Fin n → ℕ) : Fin n → Zq :=
  fun i => decompress d (g i)

/-- Every coefficient of `compressPoly d f` is strictly less than `2^d`. -/
theorem compressPoly_lt (d : ℕ) (f : Fin n → Zq) (i : Fin n) :
    compressPoly d f i < 2 ^ d :=
  compress_lt_two_pow d (f i)

/-- Compressing the zero polynomial yields the zero compressed polynomial. -/
theorem compressPoly_zero (d : ℕ) :
    compressPoly d (fun _ => (0 : Zq)) = fun _ => 0 := by
  funext i; exact compress_zero d

/-- Decompressing the zero compressed polynomial yields the zero polynomial. -/
theorem decompressPoly_zero (d : ℕ) (hd : 1 ≤ d) :
    decompressPoly d (fun _ => 0) = fun _ => (0 : Zq) := by
  funext i; exact decompress_zero d hd

/-! ## Vector-level compression -/

/-- Apply `Compress_d` coefficient-wise to each polynomial in a vector `v ∈ R_q^k`. -/
def compressVec (p : ParamSet) (d : ℕ) (v : RqVec p) : Fin p.k → (Fin n → ℕ) :=
  fun j => compressPoly d (Rq.toCoeffs (v j))

/-- Apply `Decompress_d` coefficient-wise to each compressed polynomial in a vector. -/
def decompressVec (p : ParamSet) (d : ℕ)
    (g : Fin p.k → (Fin n → ℕ)) : RqVec p :=
  fun j => Rq.ofCoeffs (decompressPoly d (g j))

/-! ## Round-trip error bound -/

/-- The maximum round-trip error: `compressError d = ⌈q / 2^{d+1}⌉`. -/
def compressError (d : ℕ) : ℕ := (q + 2 ^ (d + 1) - 1) / 2 ^ (d + 1)

/-- The compression error for `d_v = 4` evaluates to 105. -/
@[simp] theorem compressError_4 : compressError 4 = 105 := by grind [compressError]

/-- The compression error for `d_u = 10` evaluates to 2. -/
@[simp] theorem compressError_10 : compressError 10 = 2 := by grind [compressError]

/-! ## ML-KEM-768 instantiations -/

/-- Compress a polynomial with depth `d_u = 10`. -/
def compressPolyDu : (Fin n → Zq) → (Fin n → ℕ) := compressPoly mlkem768.d_u

/-- Compress a polynomial with depth `d_v = 4`. -/
def compressPolyDv : (Fin n → Zq) → (Fin n → ℕ) := compressPoly mlkem768.d_v

/-- Decompress a polynomial with depth `d_u = 10`. -/
def decompressPolyDu : (Fin n → ℕ) → (Fin n → Zq) := decompressPoly mlkem768.d_u

/-- Decompress a polynomial with depth `d_v = 4`. -/
def decompressPolyDv : (Fin n → ℕ) → (Fin n → Zq) := decompressPoly mlkem768.d_v

/-- Compress a vector with depth `d_u = 10`. -/
def compressVecDu : RqVec mlkem768 → Fin mlkem768.k → (Fin n → ℕ) :=
  compressVec mlkem768 mlkem768.d_u

/-- Decompress a vector with depth `d_u = 10`. -/
def decompressVecDu : (Fin mlkem768.k → (Fin n → ℕ)) → RqVec mlkem768 :=
  decompressVec mlkem768 mlkem768.d_u

end Fips203
