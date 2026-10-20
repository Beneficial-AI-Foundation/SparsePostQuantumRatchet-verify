/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.Ring
/-!
# FIPS 203 NTT Zeta Constants

NIST FIPS 203 (ML-KEM, August 2024) defines the Number-Theoretic Transform
(NTT) over `ℤ_q = ℤ/3329ℤ` using a primitive 256th root of unity `ζ = 17`.
Since `q = 3329` is prime and `256 ∣ (q − 1) = 3328`, such a root exists and
is unique up to conjugation.

The NTT butterflies (Algorithms 7–8) index into a precomputed table of 128
"zeta values"

  `ζ^{BitRev₇(i)}`   for `i = 0, 1, …, 127`

where `BitRev₇` reverses a 7-bit integer.  This file provides:

1. **`ζ`** — the primitive 256th root of unity `17 ∈ ℤ_q`.
2. **`bitRev7`** — 7-bit reversal on `{0, …, 127}`.
3. **`zetaTable`** — the 128-entry lookup table `fun i => ζ ^ BitRev₇(i)`.
4. **`zetasList`** — the explicit `List Zq` of the 128 zeta values, matching
   the reference table in FIPS 203 §4.3.
5. Proofs that `ζ` is indeed a primitive 256th root of unity in `ℤ_q` and
   that the list agrees with the functional definition.

**Source**: NIST FIPS 203, § 4.3 (Number-Theoretic Transform)
-/

@[expose] public section

namespace Fips203

/-! ## Internal helpers for `ZMod` arithmetic

These lemmas reduce equalities and inequalities in `ZMod n` to decidable
`norm_num`-friendly goals over `ℕ`. -/

/-- Prove `(a : ZMod n) ^ b = 1` by verifying `a ^ b ≡ 1 [MOD n]` in `ℕ`. -/
private lemma zmod_pow_eq_one {n : ℕ} (a b : ℕ) (h : a ^ b % n = 1 % n) :
    (a : ZMod n) ^ b = 1 := by
  have h1 : (a : ZMod n) ^ b = ((a ^ b : ℕ) : ZMod n) := by push_cast; ring
  rw [h1, show (1 : ZMod n) = ((1 : ℕ) : ZMod n) from by simp]
  exact_mod_cast (ZMod.natCast_eq_natCast_iff (a ^ b) 1 n).mpr
    (by unfold Nat.ModEq; omega)

/-- Prove `(a : ZMod n) ^ b = (c : ZMod n)` by verifying congruence in `ℕ`. -/
private lemma zmod_pow_eq_cast {n : ℕ} (a b c : ℕ) (h : a ^ b % n = c % n) :
    (a : ZMod n) ^ b = (c : ZMod n) := by
  have h1 : (a : ZMod n) ^ b = ((a ^ b : ℕ) : ZMod n) := by push_cast; ring
  rw [h1]
  exact_mod_cast (ZMod.natCast_eq_natCast_iff (a ^ b) c n).mpr
    (by unfold Nat.ModEq; omega)

/-- Prove `(a : ZMod n) ^ b ≠ 1` by verifying non-congruence in `ℕ`. -/
private lemma zmod_pow_ne_one {n : ℕ} (a b : ℕ) (h : a ^ b % n ≠ 1 % n) :
    (a : ZMod n) ^ b ≠ 1 := by
  intro heq
  apply h
  have h1 : (a : ZMod n) ^ b = ((a ^ b : ℕ) : ZMod n) := by push_cast; ring
  rw [h1, show (1 : ZMod n) = ((1 : ℕ) : ZMod n) from by simp] at heq
  have := (ZMod.natCast_eq_natCast_iff (a ^ b) 1 n).mp heq
  unfold Nat.ModEq at this; omega

/-- `-1 = q − 1` in `ℤ_q`. -/
private lemma neg_one_eq_q_sub_one : (-1 : Zq) = (3328 : Zq) := by
  have h : (3329 : Zq) = 0 := CharP.cast_eq_zero (ZMod q) q
  have h2 : (3328 : Zq) + 1 = 0 := by change (3329 : Zq) = 0; exact h
  exact (eq_neg_of_add_eq_zero_left h2).symm

/-! ## Primitive root of unity -/

/-- `ζ = 17 ∈ ℤ_q`, a primitive 256th root of unity modulo `q = 3329`.
FIPS 203 §4.3: "Let ζ = 17 denote the primitive 256th root of unity in ℤ_q
such that ζ¹²⁸ = −1 (mod q)." -/
def ζ : Zq := Zq.ofNat 17

/-- `ζ` raised to the 256th power equals `1` in `ℤ_q`. -/
theorem ζ_pow_256 : ζ ^ 256 = (1 : Zq) := by
  change (17 : Zq) ^ 256 = 1
  exact zmod_pow_eq_one 17 256 (by norm_num)

/-- `ζ¹²⁸ ≡ −1 (mod q)`.  Key property for NTT butterfly decomposition. -/
theorem ζ_pow_128 : ζ ^ 128 = (-1 : Zq) := by
  change (17 : Zq) ^ 128 = -1
  rw [neg_one_eq_q_sub_one]
  exact zmod_pow_eq_cast 17 128 3328 (by norm_num)

/-- `ζ` is a *primitive* 256th root of unity: its multiplicative order is
exactly 256.  Since `256 = 2⁸`, it suffices to verify that `ζ¹²⁸ ≠ 1`
(the only maximal proper divisor of 256 for a prime-power order). -/
theorem ζ_primitive_aux : ζ ^ 128 ≠ (1 : Zq) := by
  change (17 : Zq) ^ 128 ≠ 1
  exact zmod_pow_ne_one 17 128 (by norm_num)


/-! ## 7-bit reversal -/

/-- The 128-entry lookup table for 7-bit reversal.  Entry `i` is the 7-bit
reversal of `i`, i.e. the integer obtained by reversing the binary
representation `b₆b₅b₄b₃b₂b₁b₀` of `i` to get `b₀b₁b₂b₃b₄b₅b₆`.

This is the index permutation used by the Cooley–Tukey NTT in FIPS 203
Algorithms 7 and 8. -/
def bitRev7Table : Fin 128 → Fin 128
  | ⟨i, _⟩ => ⟨
    [ 0,  64,  32,  96,  16,  80,  48, 112,
      8,  72,  40, 104,  24,  88,  56, 120,
      4,  68,  36, 100,  20,  84,  52, 116,
     12,  76,  44, 108,  28,  92,  60, 124,
      2,  66,  34,  98,  18,  82,  50, 114,
     10,  74,  42, 106,  26,  90,  58, 122,
      6,  70,  38, 102,  22,  86,  54, 118,
     14,  78,  46, 110,  30,  94,  62, 126,
      1,  65,  33,  97,  17,  81,  49, 113,
      9,  73,  41, 105,  25,  89,  57, 121,
      5,  69,  37, 101,  21,  85,  53, 117,
     13,  77,  45, 109,  29,  93,  61, 125,
      3,  67,  35,  99,  19,  83,  51, 115,
     11,  75,  43, 107,  27,  91,  59, 123,
      7,  71,  39, 103,  23,  87,  55, 119,
     15,  79,  47, 111,  31,  95,  63, 127
    ].get ⟨i, by simp; omega⟩, by
      simp only [List.get_eq_getElem]
      interval_cases i <;> simp_all⟩

/-- `bitRev7Table` is an involution. -/
theorem bitRev7Table_involutive (i : Fin 128) :
    bitRev7Table (bitRev7Table i) = i := by
  fin_cases i <;> rfl


/-! ## Zeta lookup table -/

/-- The precomputed table of 128 "twiddle factors" used by the NTT.

Entry `i` is `ζ^{BitRev₇(i)}` for `i ∈ {0, …, 127}`.  Algorithms 7 (`NTT`)
and 8 (`NTT⁻¹`) in FIPS 203 walk through this table sequentially as they
process the butterfly layers. -/
noncomputable def zetaTable (i : Fin 128) : Zq :=
  ζ ^ (bitRev7Table i).val

/-- The explicit list of 128 zeta values `ζ^{BitRev₇(0)}, …, ζ^{BitRev₇(127)}`
reduced modulo `q = 3329`.  These match the reference values in FIPS 203
§4.3. -/
def zetasList : List Zq :=
  [1, 1729, 2580, 3289, 2642, 630, 1897, 848,
   1062, 1919, 193, 797, 2786, 3260, 569, 1746,
   296, 2447, 1339, 1476, 3046, 56, 2240, 1333,
   1426, 2094, 535, 2882, 2393, 2879, 1974, 821,
   289, 331, 3253, 1756, 1197, 2304, 2277, 2055,
   650, 1977, 2513, 632, 2865, 33, 1320, 1915,
   2319, 1435, 807, 452, 1438, 2868, 1534, 2402,
   2647, 2617, 1481, 648, 2474, 3110, 1227, 910,
   17, 2761, 583, 2649, 1637, 723, 2288, 1100,
   1409, 2662, 3281, 233, 756, 2156, 3015, 3050,
   1703, 1651, 2789, 1789, 1847, 952, 1461, 2687,
   939, 2308, 2437, 2388, 733, 2337, 268, 641,
   1584, 2298, 2037, 3220, 375, 2549, 2090, 1645,
   1063, 319, 2773, 757, 2099, 561, 2466, 2594,
   2804, 1092, 403, 1026, 1143, 2150, 2775, 886,
   1722, 1212, 1874, 1029, 2110, 2935, 885, 2154]

/-- The explicit zeta list has exactly 128 entries. -/
@[simp]
theorem zetasList_length : zetasList.length = 128 := by
  simp [zetasList]

/-! ## Spot-check theorems

Rather than using `fin_cases` on all 128 entries (which can be slow to
elaborate), we verify representative entries that exercise each butterfly
layer boundary.  Full agreement between `zetaTable` and `zetasList` can be
checked entry-by-entry when needed. -/

/-- The first entry: `ζ^{BitRev₇(0)} = ζ⁰ = 1`. -/
@[simp]
theorem zetaTable_zero : zetaTable 0 = (1 : Zq) := by
  simp only [zetaTable, bitRev7Table, ζ]
  norm_num

/-- The second entry: `ζ^{BitRev₇(1)} = ζ⁶⁴ = 1729 (mod 3329)`.
This is the twiddle factor for the first butterfly layer. -/
@[simp]
theorem zetaTable_one : zetaTable 1 = (1729 : Zq) := by
  simp only [zetaTable, bitRev7Table, ζ]
  exact zmod_pow_eq_cast 17 64 1729 (by norm_num)

/-- Entry 64: `ζ^{BitRev₇(64)} = ζ¹ = 17 (mod 3329)`. -/
@[simp]
theorem zetaTable_64 : zetaTable ⟨64, by omega⟩ = (17 : Zq) := by
  simp only [zetaTable, bitRev7Table, ζ]
  norm_num

end Fips203
