/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.Params
public import Spqr.Crypto.Fips203.Ring
public import Spqr.Crypto.Fips203.Conversion.BytesToBits
public import Spqr.Crypto.Fips203.Conversion.ByteEncode
public import Spqr.Crypto.Fips203.Conversion.RoundTrip
public import Mathlib.Tactic.Ring
/-!
# FIPS 203 Algorithm 4: `ByteDecode_d`

NIST FIPS 203 (ML-KEM, August 2024), § 4.2.1, defines `ByteDecode_d` as the conversion from
a byte array `B` of length `32·d` into an integer array `F` of length `n = 256`.  The byte
array is first unpacked into `256·d` bits via `BytesToBits` (Algorithm 2); then every `d`
consecutive bits are assembled (little-endian) into one coefficient:

  `F[i] = ∑_{j=0}^{d-1} b[i·d + j] · 2^j`     for `0 ≤ i < 256`

For `d < 12`, the result is reduced modulo `q`: `F[i] = (∑ …) mod q`.
For `d = 12`, the sum is taken as-is (since every 12-bit value is already < 4096).

Its inverse is `ByteEncode_d` (Algorithm 3).

**Source**: NIST FIPS 203, § 4.2.1, Algorithm 4
-/

@[expose] public section

namespace Fips203

/-! ## Bit-group-to-integer assembly -/

/-- Assemble `d` consecutive little-endian bits starting at position `start` into a natural
number using Horner's method (processing from the highest bit down to the lowest):

  `bitsToInt bits d start = b[start+d-1]·2^(d-1) + … + b[start+1]·2 + b[start]`

This is equivalent to `∑_{j=0}^{d-1} bits(start + j) · 2^j` but avoids computing powers
of 2 explicitly. -/
def bitsToInt {m : ℕ} (bits : Fin m → Fin 2) (d : ℕ) (start : ℕ)
    (h : start + d ≤ m) : ℕ :=
  go d h 0
where
  /-- Horner-style accumulator: processes bits from index `start + rem - 1` down to `start`,
  maintaining `acc = ∑_{j=rem}^{d-1} bits(start+j) · 2^(j-rem)` at each call. -/
  go : (rem : ℕ) → (start + rem ≤ m) → ℕ → ℕ
  | 0,       _,  acc => acc
  | rem + 1, hr, acc =>
    go rem (by omega) (2 * acc + (bits ⟨start + rem, by omega⟩).val)

/-- `bitsToInt` of all-zero bits is `0`. -/
theorem bitsToInt_zero {m : ℕ} (d : ℕ) (start : ℕ) (h : start + d ≤ m) :
    bitsToInt (fun (_ : Fin m) => (0 : Fin 2)) d start h = 0 := by
  simp only [bitsToInt]
  suffices ∀ (rem : ℕ) (hr : start + rem ≤ m),
      bitsToInt.go (fun (_ : Fin m) => (0 : Fin 2)) d start rem hr 0 = 0 by
    exact this d h
  intro rem
  induction rem with
  | zero => simp [bitsToInt.go]
  | succ n ih =>
    intro hr
    simp only [bitsToInt.go, Fin.val_zero, Nat.add_zero, Nat.mul_zero]
    exact ih (by omega)

/-- `bitsToInt` is bounded by `2^d`. -/
private theorem bitsToInt_go_lt {m : ℕ} (bits : Fin m → Fin 2) (d start : ℕ)
    (rem : ℕ) (hr : start + rem ≤ m) (acc : ℕ) (k : ℕ) (hacc : acc < 2 ^ k) :
    bitsToInt.go bits d start rem hr acc < 2 ^ (k + rem) := by
  induction rem generalizing acc k with
  | zero => simp only [bitsToInt.go, add_zero]; exact hacc
  | succ n ih =>
    simp only [bitsToInt.go]
    have key : k + (n + 1) = (k + 1) + n := by omega
    rw [key]
    apply ih
    have hb : (bits ⟨start + n, by omega⟩).val < 2 := (bits ⟨start + n, by omega⟩).isLt
    have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega

theorem bitsToInt_lt {m : ℕ} (bits : Fin m → Fin 2) (d : ℕ) (start : ℕ)
    (h : start + d ≤ m) :
    bitsToInt bits d start h < 2 ^ d := by
  unfold bitsToInt
  have := bitsToInt_go_lt bits d start d h 0 0 (by norm_num)
  simp only [zero_add] at this
  exact this

/-! ## Bit-to-coefficient reconstruction -/

/-- Reconstruct an integer array of length `n = 256` from a bit array of length `8 · (32·d)`.

Each coefficient `F[i]` is the little-endian sum of `d` consecutive bits:

  `F[i] = ∑_{j=0}^{d-1} b[i·d + j] · 2^j`     for `0 ≤ i < 256`

This corresponds to the inner loop of `ByteDecode_d`. -/
def bitsToCoeffs (d : ℕ) (b : Fin (8 * (32 * d)) → Fin 2) :
    Fin n → ℕ :=
  fun i =>
    bitsToInt b d ((i : ℕ) * d) (by
      have h1 : (i : ℕ) < n := i.isLt
      have h2 : 8 * (32 * d) = n * d := by unfold n; ring
      rw [h2]; nlinarith)

/-! ## `ByteDecode_d` -/

/-- **Algorithm 4 — `ByteDecode_d`** (FIPS 203, § 4.2.1).

Decodes a byte array `B` of length `32 · d` into an integer array `F` of length `n = 256`.

The byte array is first unpacked into bits via `BytesToBits`; then every group of `d`
consecutive bits is assembled (little-endian) into one coefficient:

  `F[i] = ∑_{j=0}^{d-1} b[i·d + j] · 2^j`

```
ByteDecode_d(B):
  b ← BytesToBits(B)
  for (i ← 0; i < 256; i++)
    F[i] ← ∑_{j=0}^{d-1} b[i·d + j] · 2^j
  return F
```

For `d < 12`, coefficients should be reduced mod `q`; use `byteDecodeZq` for that variant.
-/
def byteDecode (d : ℕ) (B : Fin (32 * d) → UInt8) : Fin n → ℕ :=
  bitsToCoeffs d (bytesToBits B)

/-- `ByteDecode_d` with mod-`q` reduction, producing elements of `ℤ_q`.

For `d < 12`, each reconstructed integer is reduced modulo `q` to yield a valid element
of `ℤ_q`.  For `d = 12`, the reduction is still well-defined. -/
def byteDecodeZq (d : ℕ) (B : Fin (32 * d) → UInt8) : Fin n → Zq :=
  fun i => Zq.ofNat (byteDecode d B i)

/-! ## Elementary properties -/

/-- `bitsToCoeffs` applied to the all-zero bit string yields the all-zero integer array. -/
theorem bitsToCoeffs_zero (d : ℕ) :
    bitsToCoeffs d (fun (_ : Fin (8 * (32 * d))) => (0 : Fin 2)) =
      fun (_ : Fin n) => 0 := by
  funext i
  simp only [bitsToCoeffs, bitsToInt_zero]

/-- `byteDecode` applied to the all-zero byte string yields the all-zero integer array. -/
theorem byteDecode_zero (d : ℕ) :
    byteDecode d (fun (_ : Fin (32 * d)) => (0 : UInt8)) = fun _ => 0 := by
  simp only [byteDecode, bytesToBits_zero]
  exact bitsToCoeffs_zero d

/-- Each coefficient produced by `byteDecode` is bounded by `2^d`. -/
theorem byteDecode_lt (d : ℕ) (B : Fin (32 * d) → UInt8) (i : Fin n) :
    byteDecode d B i < 2 ^ d := by
  simp only [byteDecode, bitsToCoeffs]
  exact bitsToInt_lt _ d _ _

/-- For `d = 12`, every coefficient is bounded by `4096`. -/
theorem byteDecode_lt_4096 (B : Fin (32 * 12) → UInt8) (i : Fin n) :
    byteDecode 12 (by omega) i < 4096 := by
  have h := byteDecode_lt 12 (by omega) i
  norm_num at h ⊢
  exact h

/-- The Horner accumulator `bitsToInt.go` satisfies:
  `go bits d start rem hr acc = acc * 2^rem + ∑_{j=0}^{rem-1} bits[start+j] * 2^j` -/
private theorem bitsToInt_go_eq_sum {m : ℕ} (bits : Fin m → Fin 2) (d start rem : ℕ)
    (hr : start + rem ≤ m) (acc : ℕ) :
    bitsToInt.go bits d start rem hr acc =
      acc * 2 ^ rem + Finset.univ.sum (fun (j : Fin rem) =>
        (bits ⟨start + j, by omega⟩).val * 2 ^ (j : ℕ)) := by
  induction rem generalizing acc with
  | zero => simp [bitsToInt.go]
  | succ k ih =>
    -- go (k+1) acc = go k (2*acc + bits[start+k])
    simp only [bitsToInt.go]
    rw [ih]
    -- RHS of ih: (2*acc + bits[start+k]) * 2^k + ∑_{j<k} bits[start+j] * 2^j
    -- Goal RHS: acc * 2^(k+1) + ∑_{j<k+1} bits[start+j] * 2^j
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    ring_nf

/-- `bitsToInt bits d start h = ∑_{j=0}^{d-1} bits[start+j] * 2^j` -/
theorem bitsToInt_eq_sum {m : ℕ} (bits : Fin m → Fin 2) (d start : ℕ)
    (h : start + d ≤ m) :
    bitsToInt bits d start h =
      Finset.univ.sum (fun (j : Fin d) =>
        (bits ⟨start + j, by omega⟩).val * 2 ^ (j : ℕ)) := by
  unfold bitsToInt
  rw [bitsToInt_go_eq_sum]
  simp

/-- When bits are produced by `coeffsToBits`, `bytesToBits ∘ bitsToBytes` cancels, and
  `bitsToInt` recovers the original coefficient via `intBit_sum_eq`. -/
private theorem coeffsToBits_access (d : ℕ) (hd : 0 < d) (F : Fin n → ℕ)
    (i : Fin n) (j : ℕ) (hj : j < d)
    (hidx : (i : ℕ) * d + j < 8 * (32 * d)) :
    (coeffsToBits d F ⟨(i : ℕ) * d + j, hidx⟩) = intBit (F i) j := by
  simp only [coeffsToBits, intBit]
  have h_comm : (i : ℕ) * d + j = d * (i : ℕ) + j := by ring
  have h_div : ((i : ℕ) * d + j) / d = (i : ℕ) := by
    rw [h_comm, Nat.mul_add_div hd]; simp [Nat.div_eq_of_lt hj]
  have h_mod : ((i : ℕ) * d + j) % d = j := by
    rw [h_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hj
  simp only [h_div, h_mod]

/-- Round-trip: `ByteDecode_d ∘ ByteEncode_d = id` on arrays bounded by `2^d`. -/
theorem byteDecode_byteEncode (d : ℕ) (hd : 0 < d) (F : Fin n → ℕ)
    (hF : ∀ i, F i < 2 ^ d) (i : Fin n) :
    byteDecode d (byteEncode d F) i = F i := by
  simp only [byteDecode, byteEncode]
  rw [bytesToBits_bitsToBytes]
  simp only [bitsToCoeffs]
  rw [bitsToInt_eq_sum]
  have key : (fun (j : Fin d) =>
      (coeffsToBits d F ⟨(i : ℕ) * d + j, by
        have hi := i.isLt; have hj := j.isLt; unfold n at *
        have : (i : ℕ) * d ≤ 255 * d := Nat.mul_le_mul_right d (by omega)
        omega⟩).val * 2 ^ (j : ℕ)) =
    (fun (j : Fin d) => (intBit (F i) j).val * 2 ^ (j : ℕ)) := by
    funext j
    congr 1
    have hidx : (i : ℕ) * d + (j : ℕ) < 8 * (32 * d) := by
      have hi := i.isLt; have hj := j.isLt; unfold n at *
      have : (i : ℕ) * d ≤ 255 * d := Nat.mul_le_mul_right d (by omega)
      omega
    rw [coeffsToBits_access d hd F i j j.isLt hidx]
  rw [key]
  exact (intBit_sum_eq (F i) d (hF i)).symm

/-- Round-trip: `ByteDecode_12 ∘ ByteEncode_12 = id` on arrays bounded by `2^12`. -/
theorem byteDecode_byteEncode_12 (F : Fin n → ℕ) (hF : ∀ i, F i < 2 ^ 12) (i : Fin n) :
    byteDecode 12 (byteEncode 12 F) i = F i :=
  byteDecode_byteEncode 12 (by omega) F hF i

/-- `ZMod.val` of an element of `ℤ_q` is less than `q`. -/
private theorem Zq_val_lt_q (x : Zq) : (x : ZMod q).val < q :=
  ZMod.val_lt x

/-- `ZMod.val` of an element of `ℤ_q` is less than `2^d` when `d ≥ 12`, since `q < 2^12`. -/
private theorem Zq_val_lt_pow (x : Zq) (d : ℕ) (hd : 12 ≤ d) :
    (x : ZMod q).val < 2 ^ d := by
  calc (x : ZMod q).val < q := Zq_val_lt_q x
    _ < 2 ^ 12 := q_lt_two_pow_12
    _ ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) hd

/-- Casting `ZMod.val x` back to `ZMod q` recovers `x`. -/
private theorem Zq_natCast_val (x : Zq) : Zq.ofNat (x.val) = x := by
  simp [Zq.ofNat]

/-- Round-trip in `ℤ_q`: `byteDecodeZq d ∘ byteEncodeZq d = id` for `d ≤ 12`.

Note: this round-trip requires that all coefficient values fit in `d` bits.
For `d = 12` this is automatic since `q = 3329 < 2^12 = 4096`.
For `d < 12` the caller must ensure the values are small enough. -/
theorem byteDecodeZq_byteEncodeZq (d : ℕ) (hd : 0 < d)
    (F : Fin n → Zq) (hval : ∀ i, (F i).val < 2 ^ d) (i : Fin n) :
    byteDecodeZq d (byteEncodeZq d F) i = F i := by
  simp only [byteDecodeZq, byteEncodeZq]
  rw [byteDecode_byteEncode d hd (fun i => (F i).val) hval i]
  exact Zq_natCast_val (F i)

/-- Specialization for `d = 12`: the bound `val < 2^12` holds automatically since `q < 2^12`. -/
theorem byteDecodeZq_byteEncodeZq_12
    (F : Fin n → Zq) (i : Fin n) :
    byteDecodeZq 12 (byteEncodeZq 12 F) i = F i :=
  byteDecodeZq_byteEncodeZq 12 (by omega) F
    (fun i => Zq_val_lt_pow (F i) 12 (le_refl _)) i

end Fips203
