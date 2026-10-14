/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum.Prime
/-!
# FIPS 203 ML-KEM Parameter Sets

NIST FIPS 203 (ML-KEM, August 2024) defines a lattice-based key encapsulation mechanism
parameterised by a small set of constants.  This file collects those constants as Lean
definitions and proves the elementary well-formedness properties that later algorithm
definitions depend on.

All three parameter sets (ML-KEM-512, ML-KEM-768, ML-KEM-1024) share the ring degree
`n = 256` and modulus `q = 3329`.  They differ in the module rank `k`, the CBD noise
parameters `η₁, η₂`, and the ciphertext compression depths `d_u, d_v`.

The SPQR project uses **ML-KEM-768** exclusively; the other two sets are included for
completeness and to enable future parameter-generic reasoning.

**Source**: NIST FIPS 203, Table 2 (§ 8)
-/

@[expose] public section

namespace Fips203

/-! ## Shared constants -/

/-- Polynomial ring degree: `R_q = ℤ_q[X] / (X²⁵⁶ + 1)`. -/
abbrev n : ℕ := 256

/-- Modulus of the coefficient ring `ℤ_q`. -/
abbrev q : ℕ := 3329

/-- `q` is prime — required to make `ZMod q` a field. -/
theorem q_prime : Nat.Prime q := by norm_num

/-- `q` is positive. -/
theorem q_pos : 0 < q := by norm_num [q]

/-- `q` is odd. -/
theorem q_odd : q % 2 = 1 := by norm_num [q]

/-- `n` is positive. -/
theorem n_pos : 0 < n := by norm_num [q]

/-- `n` divides `q - 1`, which guarantees that primitive `2n`-th roots of unity exist in `ℤ_q`
and hence that the NTT of size `n` is well-defined over `ℤ_q`. -/
theorem n_dvd_q_sub_one : n ∣ (q - 1) := ⟨13, by decide⟩

/-! ## Per-parameter-set structure -/

/-- A complete ML-KEM parameter set (FIPS 203, Table 2). -/
structure ParamSet where
  /-- Module rank (number of polynomials per vector). -/
  k : ℕ
  /-- CBD parameter for secret key / encryption error. -/
  η₁ : ℕ
  /-- CBD parameter for encryption noise. -/
  η₂ : ℕ
  /-- Ciphertext compression depth for the vector component `u`. -/
  compressionU : ℕ
  /-- Ciphertext compression depth for the polynomial component `v`. -/
  compressionV : ℕ
  /-- `k ≥ 2` (FIPS 203 requires `k ∈ {2, 3, 4}`). -/
  hk : 2 ≤ k
  /-- `η₁ ≥ 1`. -/
  hη₁ : 1 ≤ η₁
  /-- `η₂ ≥ 1`. -/
  hη₂ : 1 ≤ η₂
  /-- `1 ≤ compressionU < 12` (compression depth is
  bounded by the coefficient bit-width `⌈log₂ q⌉`). -/
  hCompressionU : 1 ≤ compressionU ∧ compressionU < 12
  /-- `1 ≤ compressionV < 12`. -/
  hCompressionV : 1 ≤ compressionV ∧ compressionV < 12

/-! ## Derived sizes (FIPS 203, Table 2)

All sizes are in **bytes**. -/

/-- Encryption-key size: `384 · k + 32`. -/
def ParamSet.ekSize (p : ParamSet) : ℕ := 384 * p.k + 32

/-- Decryption-key size: `768 · k + 96`. -/
def ParamSet.dkSize (p : ParamSet) : ℕ := 768 * p.k + 96

/-- Ciphertext size: `32 · (d_u · k + d_v)`. -/
def ParamSet.ctSize (p : ParamSet) : ℕ := 32 * (p.compressionU * p.k + p.compressionV)

/-- Shared-secret size: always 32 bytes. -/
@[nolint unusedArguments]
def ParamSet.ssSize (_ : ParamSet) : ℕ := 32

/-! ## Concrete parameter sets -/

/-- **ML-KEM-512** (NIST security category 1). -/
def mlkem512 : ParamSet where
  k   := 2
  η₁  := 3
  η₂  := 2
  compressionU := 10
  compressionV := 4
  hk  := by omega
  hη₁ := by omega
  hη₂ := by omega
  hCompressionU := by omega
  hCompressionV := by omega

/-- **ML-KEM-768** (NIST security category 3).  This is the parameter set used by SPQR. -/
def mlkem768 : ParamSet where
  k   := 3
  η₁  := 2
  η₂  := 2
  compressionU := 10
  compressionV := 4
  hk  := by omega
  hη₁ := by omega
  hη₂ := by omega
  hCompressionU := by omega
  hCompressionV := by omega

/-- **ML-KEM-1024** (NIST security category 5). -/
def mlkem1024 : ParamSet where
  k   := 4
  η₁  := 2
  η₂  := 2
  compressionU := 11
  compressionV := 5
  hk  := by omega
  hη₁ := by omega
  hη₂ := by omega
  hCompressionU := by omega
  hCompressionV := by omega

/-! ## Derived-size evaluations for ML-KEM-768

These are the concrete values that appear in SPQR's size-level postconditions. -/

@[simp] theorem mlkem768_k : mlkem768.k   = 3  := rfl
@[simp] theorem mlkem768_η₁ : mlkem768.η₁  = 2  := rfl
@[simp] theorem mlkem768_η₂ : mlkem768.η₂  = 2  := rfl
@[simp] theorem mlkem768CompressionU : mlkem768.compressionU = 10 := rfl
@[simp] theorem mlkem768CompressionV : mlkem768.compressionV = 4  := rfl

/-- Encryption-key size for ML-KEM-768: `384 · 3 + 32 = 1184` bytes. -/
@[simp] theorem mlkem768_ekSize : mlkem768.ekSize = 1184 := by
  simp only [ParamSet.ekSize, mlkem768]

/-- Decryption-key size for ML-KEM-768: `768 · 3 + 96 = 2400` bytes. -/
@[simp] theorem mlkem768_dkSize : mlkem768.dkSize = 2400 := by
  simp only [ParamSet.dkSize, mlkem768]

/-- Ciphertext size for ML-KEM-768: `32 · (10 · 3 + 4) = 1088` bytes. -/
@[simp] theorem mlkem768_ctSize : mlkem768.ctSize = 1088 := by
  simp only [ParamSet.ctSize, mlkem768]

/-- Shared-secret size for ML-KEM-768: `32` bytes. -/
@[simp] theorem mlkem768_ssSize : mlkem768.ssSize = 32 := rfl

end Fips203
