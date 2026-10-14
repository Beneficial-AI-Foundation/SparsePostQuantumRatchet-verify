/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.NTT.Zetas
/-!
# FIPS 203 Algorithm 10 — BaseCaseMultiply

NIST FIPS 203 (ML-KEM, August 2024), § 4.3, defines `BaseCaseMultiply` as the
multiplication of two degree-1 polynomials `(a₀ + a₁X)` and `(b₀ + b₁X)` in the
quotient ring `ℤ_q[X] / (X² − γ)`, where `γ` is a power of `ζ = 17 ∈ ℤ_q`.

The NTT representation decomposes into 128 pairs of coefficients
`(fh[2i], fh[2i+1])`, each representing an element of
`ℤ_q[X] / (X² − ζ^{2·BitRev₇(i)+1})`.  The componentwise product of two
NTT-domain polynomials (Algorithm 9, `MultiplyNTTs`) applies
`BaseCaseMultiply` to each of these 128 pairs independently.

**Pseudocode** (FIPS 203, Algorithm 10):

```
BaseCaseMultiply(a₀, a₁, b₀, b₁, γ):
  c₀ ← a₀ · b₀ + a₁ · b₁ · γ
  c₁ ← a₀ · b₁ + a₁ · b₀
  return (c₀, c₁)
```

**Source**: NIST FIPS 203, § 4.3 (Algorithm 10)
-/

@[expose] public section

noncomputable section

namespace Fips203

/-! ## BaseCaseMultiply definition -/

/-- `BaseCaseMultiply(a₀, a₁, b₀, b₁, γ)` — multiply two degree-1 polynomials
`(a₀ + a₁·X)` and `(b₀ + b₁·X)` modulo `(X² − γ)` in `ℤ_q`.

Returns `(c₀, c₁)` where `c₀ = a₀·b₀ + a₁·b₁·γ` and `c₁ = a₀·b₁ + a₁·b₀`.

This is the base-case operation used by `MultiplyNTTs` (Algorithm 9). -/
def baseCaseMultiply (a₀ a₁ b₀ b₁ γ : Zq) : Zq × Zq :=
  (a₀ * b₀ + a₁ * b₁ * γ, a₀ * b₁ + a₁ * b₀)

/-! ## Elementary algebraic properties -/

/-- Commutativity: `BaseCaseMultiply(a, b, γ) = BaseCaseMultiply(b, a, γ)`. -/
theorem baseCaseMultiply_comm (a₀ a₁ b₀ b₁ γ : Zq) :
    baseCaseMultiply a₀ a₁ b₀ b₁ γ = baseCaseMultiply b₀ b₁ a₀ a₁ γ := by
  simp only [baseCaseMultiply, Prod.mk.injEq]; constructor <;> ring

/-- Multiplying by the identity `(1, 0)` on the left. -/
theorem baseCaseMultiply_one_left (a₀ a₁ γ : Zq) :
    baseCaseMultiply 1 0 a₀ a₁ γ = (a₀, a₁) := by
  simp only [baseCaseMultiply, Prod.mk.injEq]; constructor <;> ring

/-- Multiplying by the identity `(1, 0)` on the right. -/
theorem baseCaseMultiply_one_right (a₀ a₁ γ : Zq) :
    baseCaseMultiply a₀ a₁ 1 0 γ = (a₀, a₁) := by
  simp only [baseCaseMultiply, Prod.mk.injEq]; constructor <;> ring

/-- Multiplying by `(0, 0)` yields `(0, 0)`. -/
theorem baseCaseMultiply_zero_left (a₀ a₁ γ : Zq) :
    baseCaseMultiply 0 0 a₀ a₁ γ = (0, 0) := by
  simp only [baseCaseMultiply, Prod.mk.injEq]; constructor <;> ring

/-- Multiplying by `(0, 0)` on the right yields `(0, 0)`. -/
theorem baseCaseMultiply_zero_right (a₀ a₁ γ : Zq) :
    baseCaseMultiply a₀ a₁ 0 0 γ = (0, 0) := by
  simp only [baseCaseMultiply, Prod.mk.injEq]; constructor <;> ring

/-- Scalar multiplication distributes through the first factor. -/
theorem baseCaseMultiply_smul_left (c a₀ a₁ b₀ b₁ γ : Zq) :
    baseCaseMultiply (c * a₀) (c * a₁) b₀ b₁ γ =
      (c * (baseCaseMultiply a₀ a₁ b₀ b₁ γ).1,
       c * (baseCaseMultiply a₀ a₁ b₀ b₁ γ).2) := by
  simp only [baseCaseMultiply, Prod.mk.injEq]; constructor <;> ring

/-- Scalar multiplication distributes through the second factor. -/
theorem baseCaseMultiply_smul_right (c a₀ a₁ b₀ b₁ γ : Zq) :
    baseCaseMultiply a₀ a₁ (c * b₀) (c * b₁) γ =
      (c * (baseCaseMultiply a₀ a₁ b₀ b₁ γ).1,
       c * (baseCaseMultiply a₀ a₁ b₀ b₁ γ).2) := by
  simp only [baseCaseMultiply, Prod.mk.injEq]; constructor <;> ring

/-- Right-distributivity over addition in the second factor. -/
theorem baseCaseMultiply_add_right (a₀ a₁ b₀ b₁ b₀' b₁' γ : Zq) :
    baseCaseMultiply a₀ a₁ (b₀ + b₀') (b₁ + b₁') γ =
      ((baseCaseMultiply a₀ a₁ b₀ b₁ γ).1 +
         (baseCaseMultiply a₀ a₁ b₀' b₁' γ).1,
       (baseCaseMultiply a₀ a₁ b₀ b₁ γ).2 +
         (baseCaseMultiply a₀ a₁ b₀' b₁' γ).2) := by
  simp only [baseCaseMultiply, Prod.mk.injEq]; constructor <;> ring

/-- Left-distributivity over addition in the first factor. -/
theorem baseCaseMultiply_add_left (a₀ a₁ a₀' a₁' b₀ b₁ γ : Zq) :
    baseCaseMultiply (a₀ + a₀') (a₁ + a₁') b₀ b₁ γ =
      ((baseCaseMultiply a₀ a₁ b₀ b₁ γ).1 +
         (baseCaseMultiply a₀' a₁' b₀ b₁ γ).1,
       (baseCaseMultiply a₀ a₁ b₀ b₁ γ).2 +
         (baseCaseMultiply a₀' a₁' b₀ b₁ γ).2) := by
  simp only [baseCaseMultiply, Prod.mk.injEq]; constructor <;> ring

/-! ## MultiplyNTTs (Algorithm 9) — Componentwise NTT multiplication -/

/-- The twiddle factor `γᵢ = ζ^{2·BitRev₇(i)+1}` for the `i`-th coefficient
pair.  In the NTT domain, pair `(fh[2i], fh[2i+1])` lives in
`ℤ_q[X] / (X² − γᵢ)`. -/
def gammaForPair (i : Fin 128) : Zq :=
  ζ ^ (2 * (bitRev7Table i).val + 1)

/-- `MultiplyNTTs(fh, gh)` — componentwise multiplication of two NTT-domain
polynomials.  For each `i ∈ {0, …, 127}`, applies `BaseCaseMultiply` to the
coefficient pairs `(fh[2i], fh[2i+1])` and `(gh[2i], gh[2i+1])` with
twiddle factor `γᵢ = ζ^{2·BitRev₇(i)+1}`.

**Source**: NIST FIPS 203, § 4.3 (Algorithm 9) -/
def multiplyNTTs (fh gh : Fin n → Zq) : Fin n → Zq := fun idx =>
  have h_idx : idx.val < 256 := idx.isLt
  have h_div : 2 * (idx.val / 2) ≤ idx.val := Nat.mul_div_le idx.val 2
  let i : Fin 128 := ⟨idx.val / 2, by omega⟩
  let γ := gammaForPair i
  let a₀ := fh ⟨2 * i.val, by change 2 * (idx.val / 2) < 256; omega⟩
  let a₁ := fh ⟨2 * i.val + 1, by change 2 * (idx.val / 2) + 1 < 256; omega⟩
  let b₀ := gh ⟨2 * i.val, by change 2 * (idx.val / 2) < 256; omega⟩
  let b₁ := gh ⟨2 * i.val + 1, by change 2 * (idx.val / 2) + 1 < 256; omega⟩
  let (c₀, c₁) := baseCaseMultiply a₀ a₁ b₀ b₁ γ
  if idx.val % 2 = 0 then c₀ else c₁

/-- Commutativity: `MultiplyNTTs(fh, gh) = MultiplyNTTs(gh, fh)`. -/
theorem multiplyNTTs_comm (fh gh : Fin n → Zq) :
    multiplyNTTs fh gh = multiplyNTTs gh fh := by
  ext idx
  simp only [multiplyNTTs, baseCaseMultiply]
  split <;> ring

/-- Multiplying by `0` yields `0`. -/
theorem multiplyNTTs_zero_left (fh : Fin n → Zq) :
    multiplyNTTs (fun _ => 0) fh = fun _ => 0 := by
  ext idx
  simp only [multiplyNTTs, baseCaseMultiply]
  split <;> ring

/-- Scalar multiplication:
`MultiplyNTTs(c · fh, gh) = c · MultiplyNTTs(fh, gh)`. -/
theorem multiplyNTTs_smul_left (c : Zq) (fh gh : Fin n → Zq) :
    multiplyNTTs (fun i => c * fh i) gh =
      fun i => c * multiplyNTTs fh gh i := by
  ext idx
  simp only [multiplyNTTs, baseCaseMultiply]
  split <;> ring

/-- Scalar multiplication on the right:
`MultiplyNTTs(fh, c · gh) = c · MultiplyNTTs(fh, gh)`. -/
theorem multiplyNTTs_smul_right (c : Zq) (fh gh : Fin n → Zq) :
    multiplyNTTs fh (fun i => c * gh i) =
      fun i => c * multiplyNTTs fh gh i := by
  ext idx
  simp only [multiplyNTTs, baseCaseMultiply]
  split <;> ring

end Fips203
