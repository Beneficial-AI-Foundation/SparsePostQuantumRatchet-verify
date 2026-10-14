/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.Params
public import Spqr.Crypto.Fips203.Ring
public import Mathlib.Tactic.Ring
/-!
# FIPS 203 Algorithm 5: `SampleNTT`

NIST FIPS 203 (ML-KEM, August 2024), § 4.2.2, defines `SampleNTT` as rejection sampling from
an extendable-output function (XOF) byte stream to produce a polynomial in the NTT domain.

The XOF (SHAKE-128) generates a stream of bytes consumed three bytes at a time.  Each triple
`(B[3i], B[3i+1], B[3i+2])` is decoded into two candidate coefficients:

  `d₁ = B[3i]     + 256 · (B[3i+1] mod 16)`
  `d₂ = B[3i+1]/16 + 16  · B[3i+2]`

Each candidate is accepted as the next NTT coefficient iff it is `< q = 3329`.  The process
terminates once all 256 coefficients have been filled.

**Source**: NIST FIPS 203, § 4.2.2, Algorithm 5
-/

@[expose] public section

namespace Fips203

/-! ## XOF byte stream (axiomatised) -/

/-- An opaque model of the SHAKE-128 XOF.  Given a 34-byte seed (`ρ ‖ i ‖ j`), produces
an infinite stream of pseudo-random bytes. -/
opaque xof (seed : Fin 34 → UInt8) : ℕ → UInt8

/-! ## Candidate extraction from byte triples -/

/-- First candidate: `d₁ = b₀ + 256 · (b₁ mod 16)`, yielding a value in `{0,…,4095}`. -/
def d₁ (b₀ b₁ : UInt8) : ℕ :=
  b₀.toNat + 256 * (b₁.toNat % 16)

/-- Second candidate: `d₂ = ⌊b₁/16⌋ + 16 · b₂`, yielding a value in `{0,…,4095}`. -/
def d₂ (b₁ b₂ : UInt8) : ℕ :=
  b₁.toNat / 16 + 16 * b₂.toNat

/-! ## Bounds on candidates -/

/-- `d₁` is bounded by `4096 = 2¹²`. -/
theorem d₁_lt (b₀ b₁ : UInt8) : d₁ b₀ b₁ < 4096 := by
  unfold d₁
  have hb₀ := UInt8.toNat_lt b₀
  have hb₁_mod : b₁.toNat % 16 < 16 := Nat.mod_lt _ (by omega)
  omega

/-- `d₂` is bounded by `4096 = 2¹²`. -/
theorem d₂_lt (b₁ b₂ : UInt8) : d₂ b₁ b₂ < 4096 := by
  unfold d₂
  have hb₁_div : b₁.toNat / 16 < 16 :=
    Nat.div_lt_of_lt_mul (by have := UInt8.toNat_lt b₁; omega)
  have hb₂ := UInt8.toNat_lt b₂
  omega

/-! ## Rejection-sampling loop state -/

/-- State of the rejection-sampling loop: partially filled coefficient array and counter. -/
structure SampleState where
  /-- The (partial) coefficient array.  Indices `≥ ctr` are uninitialised (zero). -/
  coeffs : Fin n → Zq
  /-- Number of coefficients accepted so far. -/
  ctr    : ℕ
  /-- `ctr ≤ 256`. -/
  h_ctr  : ctr ≤ n

/-- Initial sampling state: all coefficients zero, counter at 0. -/
def SampleState.init : SampleState where
  coeffs := fun _ => 0
  ctr    := 0
  h_ctr  := by omega

/-- Accept value `v` at position `ctr`, incrementing the counter. -/
def SampleState.accept (s : SampleState) (v : Zq) (h : s.ctr < n) : SampleState where
  coeffs := Function.update s.coeffs ⟨s.ctr, h⟩ v
  ctr    := s.ctr + 1
  h_ctr  := by omega

/-! ## Core rejection step -/

/-- Accept candidate `d` if `d < q` and the array is not yet full. -/
def tryAccept (s : SampleState) (d : ℕ) : SampleState :=
  if h_full : s.ctr < n then
    if d < q then s.accept (Zq.ofNat d) h_full else s
  else s

/-- Process one byte triple at index `j`, testing both candidates `d₁` and `d₂`. -/
def processTriple (s : SampleState) (stream : ℕ → UInt8) (j : ℕ) : SampleState :=
  tryAccept (tryAccept s (d₁ (stream (3 * j)) (stream (3 * j + 1))))
    (d₂ (stream (3 * j + 1)) (stream (3 * j + 2)))

/-! ## Recursive sampling loop -/

/-- Process at most `fuel` byte triples starting from index `j`.  Terminates early once
all 256 coefficients are accepted. -/
def sampleLoop (stream : ℕ → UInt8) (s : SampleState) (j : ℕ) :
    (fuel : ℕ) → SampleState
  | 0        => s
  | fuel + 1 =>
    if s.ctr = n then s
    else sampleLoop stream (processTriple s stream j) (j + 1) fuel

/-! ## Top-level definition -/

/-- **Algorithm 5 — `SampleNTT`** (FIPS 203, § 4.2.2).

Given a 34-byte seed (`ρ ‖ i ‖ j`), produces an NTT-domain polynomial `â ∈ R_q`
(`Fin 256 → ℤ_q`) by rejection-sampling from the SHAKE-128 byte stream.

The `fuel` parameter (default 1024) bounds byte triples consumed.  With `q = 3329`
the acceptance rate is `3329/4096 ≈ 0.813`, so ≈ 315 triples suffice in expectation.

```
SampleNTT(B):
  (j, ctr) ← (0, 0)
  while ctr < 256:
    d₁ ← B[3j] + 256·(B[3j+1] mod 16)
    d₂ ← ⌊B[3j+1]/16⌋ + 16·B[3j+2]
    if d₁ < q:  â[ctr] ← d₁;  ctr ← ctr + 1
    if d₂ < q:  â[ctr] ← d₂;  ctr ← ctr + 1
    j ← j + 1
  return â
```
-/
def sampleNTT (seed : Fin 34 → UInt8) (fuel : ℕ := 1024) : Fin n → Zq :=
  (sampleLoop (xof seed) SampleState.init 0 fuel).coeffs

/-! ## Elementary properties -/

/-- `tryAccept` preserves or increments the counter by at most 1. -/
theorem tryAccept_ctr_le (s : SampleState) (d : ℕ) :
    s.ctr ≤ (tryAccept s d).ctr ∧ (tryAccept s d).ctr ≤ s.ctr + 1 := by
  unfold tryAccept
  split
  · split
    · exact ⟨by simp [SampleState.accept], by simp [SampleState.accept]⟩
    · exact ⟨le_refl _, by omega⟩
  · exact ⟨le_refl _, by omega⟩

/-- `processTriple` increments the counter by at most 2. -/
theorem processTriple_ctr_le (s : SampleState) (stream : ℕ → UInt8) (j : ℕ) :
    s.ctr ≤ (processTriple s stream j).ctr ∧
    (processTriple s stream j).ctr ≤ s.ctr + 2 := by
  simp only [processTriple]
  have h₁ := tryAccept_ctr_le s (d₁ (stream (3 * j)) (stream (3 * j + 1)))
  have h₂ := tryAccept_ctr_le
    (tryAccept s (d₁ (stream (3 * j)) (stream (3 * j + 1))))
    (d₂ (stream (3 * j + 1)) (stream (3 * j + 2)))
  exact ⟨by omega, by omega⟩

/-- Once the counter reaches `n`, `sampleLoop` is idempotent. -/
theorem sampleLoop_done (stream : ℕ → UInt8) (s : SampleState) (j fuel : ℕ)
    (h : s.ctr = n) :
    sampleLoop stream s j fuel = s := by
  induction fuel with
  | zero => simp [sampleLoop]
  | succ fuel _ => simp [sampleLoop, h]

/-- The counter never exceeds `n` after `sampleLoop`. -/
theorem sampleLoop_ctr_le_n (stream : ℕ → UInt8) (s : SampleState)
    (j fuel : ℕ) :
    (sampleLoop stream s j fuel).ctr ≤ n := by
  induction fuel generalizing s j with
  | zero => simp only [sampleLoop]; exact s.h_ctr
  | succ fuel ih =>
    simp only [sampleLoop]
    split
    · exact s.h_ctr
    · exact ih _ _

end Fips203
