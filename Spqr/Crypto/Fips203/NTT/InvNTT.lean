/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Crypto.Fips203.NTT.NTT
/-!
# FIPS 203 Algorithm 8 — Inverse Number-Theoretic Transform (NTT⁻¹)

NIST FIPS 203 (ML-KEM, August 2024), § 4.3, defines the inverse Number-Theoretic
Transform (NTT⁻¹) that converts a polynomial `f̂` from NTT domain back to coefficient
representation.  The inverse NTT is a Gentleman–Sande decimation-in-frequency butterfly
operating in-place over 7 layers, using precomputed powers of `ζ = 17 ∈ ℤ_q` read from
the zeta table in **reverse** order.  After all butterfly layers, every coefficient is
multiplied by `n⁻¹ = 128⁻¹ = 3303 (mod 3329)` (128 = 2⁷, matching the 7 butterfly layers).

**Pseudocode** (FIPS 203, Algorithm 8):

```
NTT⁻¹(f̂):
  k ← 127
  for len in {2, 4, 8, 16, 32, 64, 128}:
    for start in {0, 2·len, …, 256 − 2·len}:
      ζ_k ← zetaTable[k];  k ← k − 1
      for j in {start, …, start + len − 1}:
        t ← f̂[j]
        f̂[j]     ← t + f̂[j + len]
        f̂[j+len] ← ζ_k · (f̂[j+len] − t)
  for i in {0, …, 255}:
    f̂[i] ← f̂[i] · 3303
  return f̂
```

**Source**: NIST FIPS 203, § 4.3 (Algorithm 8)
-/

noncomputable section

namespace Fips203

/-! ## Scaling constant `n⁻¹ mod q` -/

/-- `n⁻¹ = 128⁻¹ = 3303 (mod 3329)`.  This is the final scaling factor
applied after all 7 butterfly layers in Algorithm 8.  Since the FIPS 203
NTT is an incomplete (7-layer) transform, the scaling factor is `128⁻¹`,
not `256⁻¹`. -/
def nInv : Zq := Zq.ofNat 3303

/-- `3303 · 128 ≡ 1 (mod 3329)`. -/
theorem nInv_mul_n : nInv * (Zq.ofNat 128) = (1 : Zq) := by
  change (3303 : Zq) * (128 : Zq) = 1
  have h1 : (3303 : Zq) * (128 : Zq) = ((3303 * 128 : ℕ) : Zq) := by
    push_cast; ring
  rw [h1, show (1 : Zq) = ((1 : ℕ) : Zq) from by simp]
  exact_mod_cast (ZMod.natCast_eq_natCast_iff (3303 * 128) 1 q).mpr
    (by unfold Nat.ModEq; grind)

/-- `128 · 3303 ≡ 1 (mod 3329)`. -/
theorem n_mul_nInv : (Zq.ofNat 128) * nInv = (1 : Zq) := by
  rw [mul_comm]; exact nInv_mul_n
/-! ## Gentleman–Sande butterfly operation -/

/-- A single Gentleman–Sande butterfly on coefficient array `f̂` with twiddle
factor `ζ_k` at positions `j` and `jLen = j + len`. -/
def invNttButterfly (f : Fin n → Zq) (ζ_k : Zq) (j jLen : Fin n) :
    Fin n → Zq :=
  let t := f j
  Function.update (Function.update f j (t + f jLen)) jLen (ζ_k * (f jLen - t))

/-! ## Inner loop (j-loop) -/

/-- Execute `count` inverse butterflies at consecutive positions. -/
def invNttInnerLoop (f : Fin n → Zq) (ζ_k : Zq)
    (start len count : ℕ)
    (h1 : ∀ r, r < count → start + r < n)
    (h2 : ∀ r, r < count → start + r + len < n) :
    Fin n → Zq :=
  match count with
  | 0 => f
  | c + 1 =>
    let j    : Fin n := ⟨start, by have := h1 0 (by omega); omega⟩
    let jLen : Fin n := ⟨start + len, by have := h2 0 (by omega); omega⟩
    invNttInnerLoop (invNttButterfly f ζ_k j jLen) ζ_k (start + 1) len c
      (fun r hr => by have := h1 (r + 1) (by omega); omega)
      (fun r hr => by have := h2 (r + 1) (by omega); omega)

/-! ## Middle loop (start-loop) -/

/-- Process `numBlocks` blocks, consuming zeta entries from `k` downward. -/
def invNttMiddleLoop (f : Fin n → Zq) (len : ℕ)
    (startOff k numBlocks : ℕ)
    (h_pos : 0 < len)
    (h_fit : ∀ b, b < numBlocks → startOff + b * (2 * len) + 2 * len ≤ n)
    (h_k : ∀ b, b < numBlocks → k - b < 128)
    (h_nb : numBlocks ≤ k + 1) :
    (Fin n → Zq) × ℕ :=
  match numBlocks with
  | 0 => (f, k)
  | nb + 1 =>
    let ζ_k := zetaTable ⟨k, by have := h_k 0 (by omega); omega⟩
    let f' := invNttInnerLoop f ζ_k startOff len len
      (fun r hr => by have := h_fit 0 (by omega); omega)
      (fun r hr => by have := h_fit 0 (by omega); omega)
    invNttMiddleLoop f' len (startOff + 2 * len) (k - 1) nb h_pos
      (fun b hb => by
        have h := h_fit (b + 1) (by omega)
        change startOff + 2 * len + b * (2 * len) + 2 * len ≤ n
        nlinarith)
      (fun b hb => by have := h_k (b + 1) (by omega); omega)
      (by omega)

/-- The second component of `invNttMiddleLoop` is `k − numBlocks`. -/
theorem invNttMiddleLoop_snd (f : Fin n → Zq) (len startOff k numBlocks : ℕ)
    (h_pos : 0 < len)
    (h_fit : ∀ b, b < numBlocks → startOff + b * (2 * len) + 2 * len ≤ n)
    (h_k : ∀ b, b < numBlocks → k - b < 128)
    (h_nb : numBlocks ≤ k + 1) :
    (invNttMiddleLoop f len startOff k numBlocks h_pos h_fit h_k h_nb).2 =
      k - numBlocks := by
  induction numBlocks generalizing f startOff k with
  | zero => simp [invNttMiddleLoop]
  | succ nb ih =>
    simp only [invNttMiddleLoop]
    rw [ih]
    have := h_k 0 (by omega)
    omega


/-! ## Final scaling -/

/-- Multiply every coefficient by `n⁻¹ = 3303 (mod 3329)`. -/
def invNttScale (f : Fin n → Zq) : Fin n → Zq :=
  fun i => nInv * f i

/-! ## Outer loop (layer loop) -/

/-- The block lengths for the 7 inverse NTT layers, in order. -/
def invNttLens : List ℕ := [2, 4, 8, 16, 32, 64, 128]

@[simp] theorem invNttLens_length : invNttLens.length = 7 := by
  simp [invNttLens]

/-- Process layers with given block lengths, threading zeta index `k`
downward. -/
def invNttOuterLoop (f : Fin n → Zq) (k : ℕ) :
    (layers : List ℕ) →
    (h_layers : ∀ l ∈ layers, 0 < l ∧ 2 * l ∣ n) →
    (h_k : k + 1 ≥ (layers.map (fun l => n / (2 * l))).sum) →
    (h_k128 : k < 128) →
    (Fin n → Zq) × ℕ
  | [], _, _, _ => (f, k)
  | len :: rest, h_layers, h_k, h_k128 =>
    have h_mem := h_layers len List.mem_cons_self
    let numBlocks := n / (2 * len)
    let result := invNttMiddleLoop f len 0 k numBlocks h_mem.1
      (fun b hb => by
        simp only [numBlocks] at hb ⊢
        have h_dvd := Nat.div_mul_cancel h_mem.2
        have h_le : b * (2 * len) + 2 * len ≤ n := by
          have : (b + 1) * (2 * len) ≤ n := by
            rw [← h_dvd]
            exact Nat.mul_le_mul_right _ (by omega)
          linarith [Nat.mul_comm (b + 1) (2 * len)]
        omega)
      (fun b hb => by
        simp only [numBlocks] at hb
        omega)
      (by
        simp only [List.map_cons, List.sum_cons] at h_k
        omega)
    invNttOuterLoop result.1 result.2 rest
      (fun l hl => h_layers l (List.mem_cons_of_mem _ hl))
      (by
        simp only [List.map_cons, List.sum_cons] at h_k
        have h_fit : ∀ b, b < numBlocks → 0 + b * (2 * len) + 2 * len ≤ n := by
          intro b hb
          simp only [numBlocks] at hb ⊢
          have h_dvd := Nat.div_mul_cancel h_mem.2
          have h_le : b * (2 * len) + 2 * len ≤ n := by
            have : (b + 1) * (2 * len) ≤ n := by
              rw [← h_dvd]
              exact Nat.mul_le_mul_right _ (by omega)
            linarith [Nat.mul_comm (b + 1) (2 * len)]
          omega
        have h_kb : ∀ b, b < numBlocks → k - b < 128 := by
          intro b hb; simp only [numBlocks] at hb; omega
        have h_snd := invNttMiddleLoop_snd f len 0 k numBlocks h_mem.1
          h_fit h_kb (by omega)
        rw [h_snd]
        omega)
      (by
        simp only [List.map_cons, List.sum_cons] at h_k
        have h_fit : ∀ b, b < numBlocks → 0 + b * (2 * len) + 2 * len ≤ n := by
          intro b hb
          simp only [numBlocks] at hb ⊢
          have h_dvd := Nat.div_mul_cancel h_mem.2
          have h_le : b * (2 * len) + 2 * len ≤ n := by
            have : (b + 1) * (2 * len) ≤ n := by
              rw [← h_dvd]
              exact Nat.mul_le_mul_right _ (by omega)
            linarith [Nat.mul_comm (b + 1) (2 * len)]
          omega
        have h_kb : ∀ b, b < numBlocks → k - b < 128 := by
          intro b hb; simp only [numBlocks] at hb; omega
        have h_snd := invNttMiddleLoop_snd f len 0 k numBlocks h_mem.1
          h_fit h_kb (by omega)
        rw [h_snd]
        grind)


/-! ## Top-level definition -/

/-- **Algorithm 8 — `NTT⁻¹(f̂)`** (FIPS 203, § 4.3).

Takes a polynomial `f̂ : Fin 256 → ℤ_q` in NTT domain and returns the
corresponding polynomial in coefficient representation.

**Source**: NIST FIPS 203, § 4.3 (Algorithm 8) -/
def invNtt (f : Fin n → Zq) : Fin n → Zq :=
  let result := invNttOuterLoop f 127 invNttLens
    (by simp [invNttLens, n])
    (by simp [invNttLens, n])
    (by omega)
  invNttScale result.1

/-! ## Structural properties -/

/-- Inverse butterfly distributes over addition. -/
private theorem invNttButterfly_add (f g : Fin n → Zq) (ζ_k : Zq)
    (j jLen : Fin n) :
    invNttButterfly (fun i => f i + g i) ζ_k j jLen =
      fun i => invNttButterfly f ζ_k j jLen i +
               invNttButterfly g ζ_k j jLen i := by
  ext i
  simp only [invNttButterfly, Function.update]
  by_cases hj : i = j <;> by_cases hjl : i = jLen <;>
  simp only [hj, hjl, ↓reduceDIte, eq_rec_constant] <;>
    (try split) <;> ring

/-- Inner loop distributes over addition. -/
private theorem invNttInnerLoop_add (f g : Fin n → Zq) (ζ_k : Zq)
    (start len count : ℕ)
    (h1 : ∀ r, r < count → start + r < n)
    (h2 : ∀ r, r < count → start + r + len < n) :
    invNttInnerLoop (fun i => f i + g i) ζ_k start len count h1 h2 =
      fun i => invNttInnerLoop f ζ_k start len count h1 h2 i +
               invNttInnerLoop g ζ_k start len count h1 h2 i := by
  induction count generalizing f g start with
  | zero => simp [invNttInnerLoop]
  | succ ct ih =>
    simp only [invNttInnerLoop]
    rw [invNttButterfly_add]
    exact ih _ _ _ _ _


/-- Middle loop distributes over addition (first component). -/
private theorem invNttMiddleLoop_add (f g : Fin n → Zq)
    (len startOff k numBlocks : ℕ)
    (h_pos : 0 < len)
    (h_fit : ∀ b, b < numBlocks → startOff + b * (2 * len) + 2 * len ≤ n)
    (h_k : ∀ b, b < numBlocks → k - b < 128)
    (h_nb : numBlocks ≤ k + 1) :
    (invNttMiddleLoop (fun i => f i + g i) len startOff k numBlocks
      h_pos h_fit h_k h_nb).1 =
      fun i => (invNttMiddleLoop f len startOff k numBlocks
        h_pos h_fit h_k h_nb).1 i +
               (invNttMiddleLoop g len startOff k numBlocks
        h_pos h_fit h_k h_nb).1 i := by
  induction numBlocks generalizing f g startOff k with
  | zero => simp [invNttMiddleLoop]
  | succ nb ih =>
    simp only [invNttMiddleLoop]
    rw [invNttInnerLoop_add]
    exact ih _ _ _ _ _ _ _

/-- Outer loop distributes over addition (first component). -/
private theorem invNttOuterLoop_add (f g : Fin n → Zq) (k : ℕ)
    (layers : List ℕ)
    (h_layers : ∀ l ∈ layers, 0 < l ∧ 2 * l ∣ n)
    (h_k : k + 1 ≥ (layers.map (fun l => n / (2 * l))).sum)
    (h_k128 : k < 128) :
    (invNttOuterLoop (fun i => f i + g i) k layers
      h_layers h_k h_k128).1 =
      fun i => (invNttOuterLoop f k layers h_layers h_k h_k128).1 i +
               (invNttOuterLoop g k layers h_layers h_k h_k128).1 i := by
  induction layers generalizing f g k with
  | nil => simp [invNttOuterLoop]
  | cons len rest ih =>
    simp only [invNttOuterLoop]
    simp only [invNttMiddleLoop_snd]
    rw [invNttMiddleLoop_add]
    exact ih _ _ _ _ _ _

/-- Linearity: `NTT⁻¹(f̂ + ĝ) = NTT⁻¹(f̂) + NTT⁻¹(ĝ)`. -/
theorem invNtt_add (f g : Fin n → Zq) :
    invNtt (fun i => f i + g i) =
      fun i => invNtt f i + invNtt g i := by
  simp only [invNtt]
  rw [invNttOuterLoop_add]
  ext i; simp only [invNttScale]; ring


/-- Inverse butterfly commutes with scalar multiplication. -/
private theorem invNttButterfly_smul (c : Zq) (f : Fin n → Zq) (ζ_k : Zq)
    (j jLen : Fin n) :
    invNttButterfly (fun i => c * f i) ζ_k j jLen =
      fun i => c * invNttButterfly f ζ_k j jLen i := by
  ext i
  simp only [invNttButterfly, Function.update]
  by_cases hj : i = j <;> by_cases hjl : i = jLen <;>
  simp only [hj, hjl, ↓reduceDIte, eq_rec_constant] <;>
    (try split) <;> ring

/-- Inner loop commutes with scalar multiplication. -/
private theorem invNttInnerLoop_smul (c : Zq) (f : Fin n → Zq) (ζ_k : Zq)
    (start len count : ℕ)
    (h1 : ∀ r, r < count → start + r < n)
    (h2 : ∀ r, r < count → start + r + len < n) :
    invNttInnerLoop (fun i => c * f i) ζ_k start len count h1 h2 =
      fun i => c * invNttInnerLoop f ζ_k start len count h1 h2 i := by
  induction count generalizing f start with
  | zero => simp [invNttInnerLoop]
  | succ ct ih =>
    simp only [invNttInnerLoop]
    rw [invNttButterfly_smul]
    exact ih _ _ _ _

/-- Middle loop commutes with scalar multiplication. -/
private theorem invNttMiddleLoop_smul (c : Zq) (f : Fin n → Zq)
    (len startOff k numBlocks : ℕ)
    (h_pos : 0 < len)
    (h_fit : ∀ b, b < numBlocks → startOff + b * (2 * len) + 2 * len ≤ n)
    (h_k : ∀ b, b < numBlocks → k - b < 128)
    (h_nb : numBlocks ≤ k + 1) :
    (invNttMiddleLoop (fun i => c * f i) len startOff k numBlocks
      h_pos h_fit h_k h_nb).1 =
      fun i => c * (invNttMiddleLoop f len startOff k numBlocks
        h_pos h_fit h_k h_nb).1 i := by
  induction numBlocks generalizing f startOff k with
  | zero => simp [invNttMiddleLoop]
  | succ nb ih =>
    simp only [invNttMiddleLoop]
    rw [invNttInnerLoop_smul]
    exact ih _ _ _ _ _ _

/-- Outer loop commutes with scalar multiplication. -/
private theorem invNttOuterLoop_smul (c : Zq) (f : Fin n → Zq) (k : ℕ)
    (layers : List ℕ)
    (h_layers : ∀ l ∈ layers, 0 < l ∧ 2 * l ∣ n)
    (h_k : k + 1 ≥ (layers.map (fun l => n / (2 * l))).sum)
    (h_k128 : k < 128) :
    (invNttOuterLoop (fun i => c * f i) k layers
      h_layers h_k h_k128).1 =
      fun i => c * (invNttOuterLoop f k layers
        h_layers h_k h_k128).1 i := by
  induction layers generalizing f k with
  | nil => simp [invNttOuterLoop]
  | cons len rest ih =>
    simp only [invNttOuterLoop]
    simp only [invNttMiddleLoop_snd]
    rw [invNttMiddleLoop_smul]
    exact ih _ _ _ _ _

/-- Scaling: `NTT⁻¹(c · f̂) = c · NTT⁻¹(f̂)`. -/
theorem invNtt_smul (c : Zq) (f : Fin n → Zq) :
    invNtt (fun i => c * f i) =
      fun i => c * invNtt f i := by
  simp only [invNtt]
  rw [invNttOuterLoop_smul]
  ext i; simp only [invNttScale]; ring

/-- `NTT⁻¹(0) = 0`. -/
theorem invNtt_zero :
    invNtt (fun _ : Fin n => (0 : Zq)) = fun _ => 0 := by
  have h := invNtt_smul (0 : Zq) (fun _ => (0 : Zq))
  simp only [zero_mul] at h
  exact h

end Fips203
