/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Crypto.Fips203.NTT.Zetas
/-!
# FIPS 203 Algorithm 7 — Number-Theoretic Transform (NTT)

NIST FIPS 203 (ML-KEM, August 2024), § 4.3, defines the forward Number-Theoretic
Transform (NTT) that converts a polynomial `f ∈ R_q` from coefficient representation
to NTT domain.  The NTT is a Cooley–Tukey decimation-in-time butterfly operating
in-place over 7 layers, using precomputed powers of `ζ = 17 ∈ ℤ_q`.

**Pseudocode** (FIPS 203, Algorithm 7):

```
NTT(f):
  k ← 1
  for len in {128, 64, 32, 16, 8, 4, 2}:
    for start in {0, 2·len, …, 256 − 2·len}:
      ζ_k ← zetaTable[k];  k ← k + 1
      for j in {start, …, start + len − 1}:
        t ← ζ_k · f[j + len];  f[j+len] ← f[j] − t;  f[j] ← f[j] + t
  return f
```

**Source**: NIST FIPS 203, § 4.3 (Algorithm 7)
-/

noncomputable section

namespace Fips203

/-! ## Butterfly operation -/

/-- A single Cooley–Tukey butterfly on coefficient array `f` with twiddle
factor `ζ_k` at positions `j` and `jLen = j + len`. -/
def nttButterfly (f : Fin n → Zq) (ζ_k : Zq) (j jLen : Fin n) :
    Fin n → Zq :=
  let t := ζ_k * f jLen
  Function.update (Function.update f jLen (f j - t)) j (f j + t)

/-! ## Inner loop (j-loop) -/

/-- Execute `count` butterflies at consecutive positions from `start`. -/
def nttInnerLoop (f : Fin n → Zq) (ζ_k : Zq)
    (start len count : ℕ)
    (h1 : ∀ r, r < count → start + r < n)
    (h2 : ∀ r, r < count → start + r + len < n) :
    Fin n → Zq :=
  match count with
  | 0 => f
  | c + 1 =>
    let j    : Fin n := ⟨start, by have := h1 0 (by omega); omega⟩
    let jLen : Fin n := ⟨start + len, by have := h2 0 (by omega); omega⟩
    nttInnerLoop (nttButterfly f ζ_k j jLen) ζ_k (start + 1) len c
      (fun r hr => by have := h1 (r + 1) (by omega); omega)
      (fun r hr => by have := h2 (r + 1) (by omega); omega)

/-! ## Middle loop (start-loop) -/

/-- Process `numBlocks` blocks of size `len`, consuming zeta entries from `k`. -/
def nttMiddleLoop (f : Fin n → Zq) (len : ℕ)
    (startOff k numBlocks : ℕ)
    (h_pos : 0 < len)
    (h_fit : ∀ b, b < numBlocks → startOff + b * (2 * len) + 2 * len ≤ n)
    (h_k : ∀ b, b < numBlocks → k + b < 128) :
    (Fin n → Zq) × ℕ :=
  match numBlocks with
  | 0 => (f, k)
  | nb + 1 =>
    let ζ_k := zetaTable ⟨k, by have := h_k 0 (by omega); omega⟩
    let f' := nttInnerLoop f ζ_k startOff len len
      (fun r hr => by have := h_fit 0 (by omega); omega)
      (fun r hr => by have := h_fit 0 (by omega); omega)
    nttMiddleLoop f' len (startOff + 2 * len) (k + 1) nb h_pos
      (fun b hb => by
        have h := h_fit (b + 1) (by omega)
        change startOff + 2 * len + b * (2 * len) + 2 * len ≤ n
        nlinarith)
      (fun b hb => by have := h_k (b + 1) (by omega); omega)

/-- The second component (zeta index) of `nttMiddleLoop` is `k + numBlocks`. -/
theorem nttMiddleLoop_snd (f : Fin n → Zq) (len startOff k numBlocks : ℕ)
    (h_pos : 0 < len)
    (h_fit : ∀ b, b < numBlocks → startOff + b * (2 * len) + 2 * len ≤ n)
    (h_k : ∀ b, b < numBlocks → k + b < 128) :
    (nttMiddleLoop f len startOff k numBlocks h_pos h_fit h_k).2 = k + numBlocks := by
  induction numBlocks generalizing f startOff k with
  | zero => simp [nttMiddleLoop]
  | succ nb ih =>
    simp only [nttMiddleLoop]
    rw [ih]
    omega

/-! ## Outer loop (len-loop)

Processes the 7 NTT layers with `len ∈ {128, 64, 32, 16, 8, 4, 2}`. -/

/-- The block lengths for the 7 NTT layers, in order. -/
def nttLens : List ℕ := [128, 64, 32, 16, 8, 4, 2]

@[simp] theorem nttLens_length : nttLens.length = 7 := by simp [nttLens]

/-- Process layers with given block lengths, threading zeta index `k`. -/
def nttOuterLoop (f : Fin n → Zq) (k : ℕ) :
    (layers : List ℕ) →
    (h_layers : ∀ l ∈ layers, 0 < l ∧ 2 * l ∣ n) →
    (h_k : k + (layers.map (fun l => n / (2 * l))).sum ≤ 128) →
    (Fin n → Zq) × ℕ
  | [], _, _ => (f, k)
  | len :: rest, h_layers, h_k =>
    have h_mem := h_layers len List.mem_cons_self
    let numBlocks := n / (2 * len)
    let result := nttMiddleLoop f len 0 k numBlocks h_mem.1
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
        have h_sum : (List.map (fun l => n / (2 * l)) (len :: rest)).sum =
               n / (2 * len) + (List.map (fun l => n / (2 * l)) rest).sum := by
          simp [List.map_cons, List.sum_cons]
        have h_nb : numBlocks = n / (2 * len) := rfl
        omega)
    nttOuterLoop result.1 result.2 rest
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
        have h_kb : ∀ b, b < numBlocks → k + b < 128 := by
          intro b hb
          simp only [numBlocks] at hb
          have : n / (2 * len) ≤ n / (2 * len) +
          (List.map (fun l => n / (2 * l)) rest).sum := Nat.le_add_right _ _
          omega
        have h_snd := nttMiddleLoop_snd f len 0 k numBlocks h_mem.1 h_fit h_kb
        rw [h_snd]
        omega)

/-! ## Top-level NTT (Algorithm 7) -/

/-- **Algorithm 7 — `NTT(f)`**: Forward Number-Theoretic Transform.

Takes `f : Fin 256 → ℤ_q` in coefficient representation and returns its
NTT-domain representation `f̂ : Fin 256 → ℤ_q`.  Applies 7 Cooley–Tukey
butterfly layers with block lengths 128, 64, 32, 16, 8, 4, 2, consuming
zeta entries `ζ^{BitRev₇(1)}` through `ζ^{BitRev₇(127)}`.

**Source**: NIST FIPS 203, § 4.3 (Algorithm 7) -/
def ntt (f : Fin n → Zq) : Fin n → Zq :=
  (nttOuterLoop f 1 nttLens
    (by simp [nttLens, n])
    (by simp [nttLens, n])).1

/-! ## Elementary properties -/

/-- Butterfly on the zero function returns zero. -/
private theorem nttButterfly_zero (ζ_k : Zq) (j jLen : Fin n) :
    nttButterfly (fun _ => (0 : Zq)) ζ_k j jLen = fun _ => (0 : Zq) := by
  ext i
  simp [nttButterfly, mul_zero, sub_self]

/-- Inner loop on the zero function returns zero. -/
private theorem nttInnerLoop_zero (ζ_k : Zq) (start len count : ℕ)
    (h1 : ∀ r, r < count → start + r < n)
    (h2 : ∀ r, r < count → start + r + len < n) :
    nttInnerLoop (fun _ => (0 : Zq)) ζ_k start len count h1 h2 = fun _ => (0 : Zq) := by
  induction count generalizing start with
  | zero => simp [nttInnerLoop]
  | succ c ih =>
    simp only [nttInnerLoop]
    rw [nttButterfly_zero]
    exact ih _ _ _

/-- Middle loop on the zero function returns zero (first component). -/
private theorem nttMiddleLoop_zero (len startOff k numBlocks : ℕ)
    (h_pos : 0 < len)
    (h_fit : ∀ b, b < numBlocks → startOff + b * (2 * len) + 2 * len ≤ n)
    (h_k : ∀ b, b < numBlocks → k + b < 128) :
    (nttMiddleLoop (fun _ => (0 : Zq)) len startOff k numBlocks h_pos h_fit h_k).1 =
      fun _ => (0 : Zq) := by
  induction numBlocks generalizing startOff k with
  | zero => simp [nttMiddleLoop]
  | succ nb ih =>
    simp only [nttMiddleLoop]
    rw [nttInnerLoop_zero]
    exact ih _ _ _ _

/-- Outer loop on the zero function returns zero (first component). -/
private theorem nttOuterLoop_zero (k : ℕ) (layers : List ℕ)
    (h_layers : ∀ l ∈ layers, 0 < l ∧ 2 * l ∣ n)
    (h_k : k + (layers.map (fun l => n / (2 * l))).sum ≤ 128) :
    (nttOuterLoop (fun _ => (0 : Zq)) k layers h_layers h_k).1 = fun _ => (0 : Zq) := by
  induction layers generalizing k with
  | nil => simp [nttOuterLoop]
  | cons len rest ih =>
    simp only [nttOuterLoop]
    rw [nttMiddleLoop_zero]
    exact ih _ _ _

/-- The NTT applied to the zero polynomial is zero. -/
theorem ntt_zero : ntt (fun _ => (0 : Zq)) = fun _ => (0 : Zq) := by
  simp only [ntt]
  exact nttOuterLoop_zero _ _ _ _

/-- Butterfly distributes over addition. -/
private theorem nttButterfly_add (f g : Fin n → Zq) (ζ_k : Zq) (j jLen : Fin n) :
    nttButterfly (fun i => f i + g i) ζ_k j jLen =
      fun i => nttButterfly f ζ_k j jLen i + nttButterfly g ζ_k j jLen i := by
  ext i
  simp only [nttButterfly]
  simp only [Function.update]
  by_cases hj : i = j <;> by_cases hjl : i = jLen <;>
  simp only [hj, ↓reduceDIte, eq_rec_constant] <;>
    (try split) <;> ring

/-- Inner loop distributes over addition. -/
private theorem nttInnerLoop_add (f g : Fin n → Zq) (ζ_k : Zq)
    (start len count : ℕ)
    (h1 : ∀ r, r < count → start + r < n)
    (h2 : ∀ r, r < count → start + r + len < n) :
    nttInnerLoop (fun i => f i + g i) ζ_k start len count h1 h2 =
      fun i => nttInnerLoop f ζ_k start len count h1 h2 i +
               nttInnerLoop g ζ_k start len count h1 h2 i := by
  induction count generalizing f g start with
  | zero => simp [nttInnerLoop]
  | succ c ih =>
    simp only [nttInnerLoop]
    rw [nttButterfly_add]
    exact ih _ _ _ _ _

/-- Middle loop distributes over addition (first component). -/
private theorem nttMiddleLoop_add (f g : Fin n → Zq) (len startOff k numBlocks : ℕ)
    (h_pos : 0 < len)
    (h_fit : ∀ b, b < numBlocks → startOff + b * (2 * len) + 2 * len ≤ n)
    (h_k : ∀ b, b < numBlocks → k + b < 128) :
    (nttMiddleLoop (fun i => f i + g i) len startOff k numBlocks h_pos h_fit h_k).1 =
      fun i => (nttMiddleLoop f len startOff k numBlocks h_pos h_fit h_k).1 i +
               (nttMiddleLoop g len startOff k numBlocks h_pos h_fit h_k).1 i := by
  induction numBlocks generalizing f g startOff k with
  | zero => simp [nttMiddleLoop]
  | succ nb ih =>
    simp only [nttMiddleLoop]
    rw [nttInnerLoop_add]
    exact ih _ _ _ _ _ _

/-- Outer loop distributes over addition (first component). -/
private theorem nttOuterLoop_add (f g : Fin n → Zq) (k : ℕ) (layers : List ℕ)
    (h_layers : ∀ l ∈ layers, 0 < l ∧ 2 * l ∣ n)
    (h_k : k + (layers.map (fun l => n / (2 * l))).sum ≤ 128) :
    (nttOuterLoop (fun i => f i + g i) k layers h_layers h_k).1 =
      fun i => (nttOuterLoop f k layers h_layers h_k).1 i +
               (nttOuterLoop g k layers h_layers h_k).1 i := by
  induction layers generalizing f g k with
  | nil => simp [nttOuterLoop]
  | cons len rest ih =>
    simp only [nttOuterLoop]
    simp only [nttMiddleLoop_snd]
    rw [nttMiddleLoop_add]
    exact ih _ _ _ _ _

/-- Linearity: `NTT(f + g) = NTT(f) + NTT(g)`. -/
theorem ntt_add (f g : Fin n → Zq) :
    ntt (fun i => f i + g i) = fun i => ntt f i + ntt g i := by
  simp only [ntt]
  exact nttOuterLoop_add _ _ _ _ _ _

/-- Butterfly commutes with scalar multiplication. -/
private theorem nttButterfly_smul (c : Zq) (f : Fin n → Zq) (ζ_k : Zq) (j jLen : Fin n) :
    nttButterfly (fun i => c * f i) ζ_k j jLen =
      fun i => c * nttButterfly f ζ_k j jLen i := by
  ext i
  simp only [nttButterfly]
  simp only [Function.update]
  by_cases hj : i = j <;> by_cases hjl : i = jLen <;>
  simp only [hj, ↓reduceDIte, eq_rec_constant] <;>
    (try split) <;> ring

/-- Inner loop commutes with scalar multiplication. -/
private theorem nttInnerLoop_smul (c : Zq) (f : Fin n → Zq) (ζ_k : Zq)
    (start len count : ℕ)
    (h1 : ∀ r, r < count → start + r < n)
    (h2 : ∀ r, r < count → start + r + len < n) :
    nttInnerLoop (fun i => c * f i) ζ_k start len count h1 h2 =
      fun i => c * nttInnerLoop f ζ_k start len count h1 h2 i := by
  induction count generalizing f start with
  | zero => simp [nttInnerLoop]
  | succ ct ih =>
    simp only [nttInnerLoop]
    rw [nttButterfly_smul]
    exact ih _ _ _ _

/-- Middle loop commutes with scalar multiplication (first component). -/
private theorem nttMiddleLoop_smul (c : Zq) (f : Fin n → Zq) (len startOff k numBlocks : ℕ)
    (h_pos : 0 < len)
    (h_fit : ∀ b, b < numBlocks → startOff + b * (2 * len) + 2 * len ≤ n)
    (h_k : ∀ b, b < numBlocks → k + b < 128) :
    (nttMiddleLoop (fun i => c * f i) len startOff k numBlocks h_pos h_fit h_k).1 =
      fun i => c * (nttMiddleLoop f len startOff k numBlocks h_pos h_fit h_k).1 i := by
  induction numBlocks generalizing f startOff k with
  | zero => simp [nttMiddleLoop]
  | succ nb ih =>
    simp only [nttMiddleLoop]
    rw [nttInnerLoop_smul]
    exact ih _ _ _ _ _

/-- Outer loop commutes with scalar multiplication (first component). -/
private theorem nttOuterLoop_smul (c : Zq) (f : Fin n → Zq) (k : ℕ) (layers : List ℕ)
    (h_layers : ∀ l ∈ layers, 0 < l ∧ 2 * l ∣ n)
    (h_k : k + (layers.map (fun l => n / (2 * l))).sum ≤ 128) :
    (nttOuterLoop (fun i => c * f i) k layers h_layers h_k).1 =
      fun i => c * (nttOuterLoop f k layers h_layers h_k).1 i := by
  induction layers generalizing f k with
  | nil => simp [nttOuterLoop]
  | cons len rest ih =>
    simp only [nttOuterLoop]
    simp only [nttMiddleLoop_snd]
    rw [nttMiddleLoop_smul]
    exact ih _ _ _ _

/-- Scaling: `NTT(c · f) = c · NTT(f)`. -/
theorem ntt_smul (c : Zq) (f : Fin n → Zq) :
    ntt (fun i => c * f i) = fun i => c * ntt f i := by
  simp only [ntt]
  exact nttOuterLoop_smul _ _ _ _ _ _

end Fips203
