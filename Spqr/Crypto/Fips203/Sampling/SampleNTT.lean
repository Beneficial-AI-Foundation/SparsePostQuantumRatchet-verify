/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.Params
public import Spqr.Crypto.Fips203.Ring
public import Spqr.Crypto.Fips203.Primitives
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

/-! ## XOF byte stream

The SHAKE-128 XOF is the `XOF` field of a `Primitives` record (`Primitives.lean`): given a
34-byte seed (`ρ ‖ i ‖ j`) it produces an unbounded stream of bytes.  The definitions below
that consume the stream take the record as an explicit argument `prims`, so every statement
about them holds for every instantiation of the XOF. -/

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

/-- Process at most `fuel` byte triples starting from index `j`.  Returns `some s'` as soon
as all 256 coefficients are accepted, and `none` if the fuel is exhausted first.

FIPS 203 Algorithm 7 loops unboundedly (`while j < 256`).  Appendix B permits a cap on the
number of iterations provided that (i) the cap is at least 280 and (ii) on reaching the cap
all intermediate results are destroyed and a single, stream-independent failure value is
returned.  Returning `none` (rather than the partially filled state) satisfies (ii): the
failure value is the same for every byte stream that exceeds the cap. -/
def sampleLoop (stream : ℕ → UInt8) (s : SampleState) (j : ℕ) :
    (fuel : ℕ) → Option SampleState
  | 0        => if s.ctr = n then some s else none
  | fuel + 1 =>
    if s.ctr = n then some s
    else sampleLoop stream (processTriple s stream j) (j + 1) fuel

/-! ## Top-level definition -/

/-- **Algorithm 5 — `SampleNTT`** (FIPS 203, § 4.2.2).

Given a 34-byte seed (`ρ ‖ i ‖ j`), produces an NTT-domain polynomial `â ∈ R_q`
(`Fin 256 → ℤ_q`) by rejection-sampling from the SHAKE-128 byte stream.

The `fuel` parameter (default 1024) bounds byte triples consumed.  With `q = 3329`
the acceptance rate is `3329/4096 ≈ 0.813`, so ≈ 315 triples suffice in expectation.
If the stream does not yield 256 accepted coefficients within `fuel` triples, `sampleNTT?`
returns `none`, and the total wrapper `sampleNTT` returns the fixed polynomial
`sampleNTTFail` (all zeros).  Both are stream-independent failure values, as required by
FIPS 203 Appendix B; crucially, no partially-filled intermediate state is ever returned.
(With a real SHAKE-128 stream the probability of exceeding even 280 iterations is ≈ 2⁻²⁶¹.)

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
def sampleNTT? (prims : Primitives) (seed : Fin 34 → UInt8) (fuel : ℕ := 1024) :
    Option (Fin n → Zq) :=
  (sampleLoop (prims.XOF seed) SampleState.init 0 fuel).map SampleState.coeffs

/-- The single, stream-independent failure value used by `sampleNTT` when the iteration
cap is exceeded (FIPS 203 Appendix B).  Chosen as the zero polynomial; what matters is
that it is a constant, not derived from any intermediate state. -/
def sampleNTTFail : Fin n → Zq := fun _ => 0

/-- Total version of `SampleNTT`: `sampleNTT?` with the constant `sampleNTTFail` on cap
exhaustion.  Convenient for downstream definitions that need a plain polynomial. -/
def sampleNTT (prims : Primitives) (seed : Fin 34 → UInt8) (fuel : ℕ := 1024) : Fin n → Zq :=
  (sampleNTT? prims seed fuel).getD sampleNTTFail

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

/-- Once the counter reaches `n`, `sampleLoop` succeeds immediately with the same state. -/
theorem sampleLoop_done (stream : ℕ → UInt8) (s : SampleState) (j fuel : ℕ)
    (h : s.ctr = n) :
    sampleLoop stream s j fuel = some s := by
  cases fuel with
  | zero => simp [sampleLoop, h]
  | succ fuel => simp [sampleLoop, h]

/-- `sampleLoop` only succeeds with a completely filled coefficient array
(`ctr = n`), so a `some` output never contains uninitialised (zero-padded) coefficients. -/
theorem sampleLoop_some_ctr (stream : ℕ → UInt8) (s : SampleState) (j fuel : ℕ)
    (s' : SampleState) (h : sampleLoop stream s j fuel = some s') :
    s'.ctr = n := by
  induction fuel generalizing s j with
  | zero =>
    simp only [sampleLoop] at h
    split at h
    · cases h; assumption
    · cases h
  | succ fuel ih =>
    simp only [sampleLoop] at h
    split at h
    · cases h; assumption
    · exact ih _ _ h

/-- The failure value is independent of the stream: whenever `sampleLoop` fails it
returns exactly `none`, carrying no intermediate state (FIPS 203 Appendix B). -/
theorem sampleLoop_fail_eq (stream₁ stream₂ : ℕ → UInt8) (s₁ s₂ : SampleState)
    (j₁ j₂ fuel₁ fuel₂ : ℕ)
    (h₁ : sampleLoop stream₁ s₁ j₁ fuel₁ = none)
    (h₂ : sampleLoop stream₂ s₂ j₂ fuel₂ = none) :
    sampleLoop stream₁ s₁ j₁ fuel₁ = sampleLoop stream₂ s₂ j₂ fuel₂ := by
  rw [h₁, h₂]

/-- A successful `sampleNTT?` is fully determined by a run that filled all `n` coefficients. -/
theorem sampleNTT?_some (prims : Primitives) (seed : Fin 34 → UInt8) (fuel : ℕ)
    (a : Fin n → Zq) (h : sampleNTT? prims seed fuel = some a) :
    ∃ s : SampleState, sampleLoop (prims.XOF seed) SampleState.init 0 fuel = some s ∧
      s.ctr = n ∧ s.coeffs = a := by
  unfold sampleNTT? at h
  cases hs : sampleLoop (prims.XOF seed) SampleState.init 0 fuel with
  | none => simp [hs] at h
  | some s =>
    refine ⟨s, rfl, sampleLoop_some_ctr _ _ _ _ _ hs, ?_⟩
    simpa [hs] using h

/-- The total `sampleNTT` either agrees with a successful `sampleNTT?`, or equals the
constant `sampleNTTFail`.  There is no third, stream-dependent outcome. -/
theorem sampleNTT_cases (prims : Primitives) (seed : Fin 34 → UInt8) (fuel : ℕ) :
    sampleNTT? prims seed fuel = some (sampleNTT prims seed fuel) ∨
    (sampleNTT? prims seed fuel = none ∧ sampleNTT prims seed fuel = sampleNTTFail) := by
  unfold sampleNTT
  cases h : sampleNTT? prims seed fuel with
  | none => exact Or.inr ⟨rfl, rfl⟩
  | some a => exact Or.inl rfl

end Fips203
