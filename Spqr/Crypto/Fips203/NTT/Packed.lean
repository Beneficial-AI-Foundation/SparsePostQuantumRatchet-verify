/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.NTT.InvNTT
/-!
# FIPS 203 NTT — packed-natural clone of Algorithm 7

A verifiable-by-computation encoding of the forward NTT (FIPS 203 § 4.3,
Algorithm 7).  A coefficient vector in `ℤ_q^{256}` is packed into a single `ℕ`
with base-4096 digits; the butterfly network is replayed on that natural so the
Lean kernel can evaluate it with GMP arithmetic.

**Source**: NIST FIPS 203, § 4.3, Algorithm 7
-/

@[expose] public section

namespace Fips203

/-! ## Packed-natural encoding

The bridge `ntt (delta j) = nttSpec (delta j)` (in `RoundTrip.lean`) is proved by a
*verified computation*:

1. a **packed-natural clone** of Algorithm 7 (`nttP`) operating on a single
   `ℕ` whose base-4096 digits are the canonical coefficient representatives,
   which the Lean kernel evaluates fast via GMP arithmetic;
2. a **simulation proof** (`simR_outerP`) showing step by step that the clone
   computes exactly the butterflies of `ntt`;
3. a **closed form** for `nttSpec (delta j)` (`nttSpec_delta`):
   `γ_{idx/2}^{j/2}` on matching parity, `0` otherwise;
4. kernel `decide +kernel` checks (`Kernel0`–`Kernel3`, 64 basis vectors
   each, combined in `KernelCheck.lean`) of all 256 basis vectors against the
   packed closed form.

This file contains only the definitions and digit-access lemmas (1–2); it
depends on nothing but `NTT.lean`, so the kernel shards compile in parallel,
each in well under 30 s. -/

/-! ### Packed-natural encoding: base-4096 digit vectors as a single `ℕ` -/

/-- Digit `j` of a base-4096 packed natural. -/
def getP (l j : ℕ) : ℕ := l / 4096 ^ j % 4096

/-- Replace digit `j` of a base-4096 packed natural by `v`. -/
def setP (l j v : ℕ) : ℕ := l - getP l j * 4096 ^ j + v * 4096 ^ j

lemma getP_zero (l : ℕ) : getP l 0 = l % 4096 := by simp [getP]

lemma getP_succ (l j : ℕ) : getP l (j + 1) = getP (l / 4096) j := by
  simp [getP, pow_succ, Nat.div_div_eq_div_mul, mul_comm]

lemma setP_zero (l v : ℕ) : setP l 0 v = l / 4096 * 4096 + v := by
  have h := Nat.div_add_mod l 4096
  have h2 : l % 4096 < 4096 := Nat.mod_lt _ (by norm_num)
  simp only [setP, getP_zero, pow_zero, mul_one]
  omega

lemma setP_succ (l j v : ℕ) :
    setP l (j + 1) v = setP (l / 4096) j v * 4096 + l % 4096 := by
  have hA := Nat.div_add_mod l 4096
  have hr : l % 4096 < 4096 := Nat.mod_lt _ (by norm_num)
  have hg : getP (l / 4096) j * 4096 ^ j ≤ l / 4096 := by
    calc getP (l / 4096) j * 4096 ^ j
        ≤ (l / 4096) / 4096 ^ j * 4096 ^ j :=
          Nat.mul_le_mul_right _ (Nat.mod_le _ _)
      _ ≤ l / 4096 := Nat.div_mul_le_self _ _
  simp only [setP, getP_succ, pow_succ]
  set A := l / 4096
  set g := getP A j
  set X := (4096 : ℕ) ^ j
  set gX := g * X with hgX
  set vX := v * X with hvX
  have e1 : g * (X * 4096) = gX * 4096 := by rw [hgX]; ring
  have e2 : v * (X * 4096) = vX * 4096 := by rw [hvX]; ring
  rw [e1, e2]
  omega

lemma getP_setP_self (l j v : ℕ) (hv : v < 4096) :
    getP (setP l j v) j = v := by
  induction j generalizing l with
  | zero =>
    rw [setP_zero, getP_zero]
    omega
  | succ j ih =>
    rw [setP_succ, getP_succ]
    have hr : l % 4096 < 4096 := Nat.mod_lt _ (by norm_num)
    have hdiv : (setP (l / 4096) j v * 4096 + l % 4096) / 4096
        = setP (l / 4096) j v := by omega
    rw [hdiv]
    exact ih _

lemma getP_setP_ne (l j v i : ℕ) (hv : v < 4096) (h : i ≠ j) :
    getP (setP l j v) i = getP l i := by
  induction j generalizing l i with
  | zero =>
    cases i with
    | zero => exact absurd rfl h
    | succ s =>
      rw [setP_zero, getP_succ, getP_succ]
      have : (l / 4096 * 4096 + v) / 4096 = l / 4096 := by omega
      rw [this]
  | succ j ih =>
    cases i with
    | zero =>
      rw [setP_succ, getP_zero, getP_zero]
      have hr : l % 4096 < 4096 := Nat.mod_lt _ (by norm_num)
      omega
    | succ s =>
      rw [setP_succ, getP_succ, getP_succ]
      have hr : l % 4096 < 4096 := Nat.mod_lt _ (by norm_num)
      have hdiv : (setP (l / 4096) j v * 4096 + l % 4096) / 4096
          = setP (l / 4096) j v := by omega
      rw [hdiv]
      exact ih _ _ (fun hc => h (by omega))

/-- Pack a little-endian list of base-4096 digits into one natural number. -/
def packList : List ℕ → ℕ
  | [] => 0
  | x :: xs => packList xs * 4096 + x

lemma getP_packList (L : List ℕ) (hb : ∀ x ∈ L, x < 4096) (i : ℕ)
    (hi : i < L.length) : getP (packList L) i = L.getD i 0 := by
  induction L generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    have hx : x < 4096 := hb x List.mem_cons_self
    cases i with
    | zero =>
      simp only [packList, getP_zero, List.getD_cons_zero]
      omega
    | succ s =>
      simp only [packList, List.getD_cons_succ]
      rw [getP_succ]
      have hdiv : (packList xs * 4096 + x) / 4096 = packList xs := by omega
      rw [hdiv]
      exact ih (fun y hy => hb y (List.mem_cons_of_mem _ hy)) s
        (by simpa using hi)

lemma getD_map_range (g : ℕ → ℕ) (m i : ℕ) (h : i < m) :
    ((List.range m).map g).getD i 0 = g i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

/-! ### The 7-bit reversal as a plain `ℕ → ℕ` table -/

/-- `bitRev7Table` as a plain `ℕ → ℕ` function (0 outside `[0,128)`),
suitable for fast kernel evaluation. -/
def brN (i : ℕ) : ℕ :=
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
   15,  79,  47, 111,  31,  95,  63, 127 ].getD i 0

set_option maxRecDepth 4000 in
lemma brN_eq_bitRev7 (i : Fin 128) : brN i.val = (bitRev7Table i).val := by
  fin_cases i <;> rfl

/-! ### Packed-natural clone of Algorithm 7 -/

/-- Packed-natural butterfly at positions `j` and `j + len`, twiddle `z`. -/
def bfP (z l j len : ℕ) : ℕ :=
  let a := getP l j
  let b := getP l (j + len)
  let t := z * b % 3329
  setP (setP l (j + len) ((a + 3329 - t) % 3329)) j ((a + t) % 3329)

/-- Packed-natural inner loop (`count` butterflies from `start`). -/
def innerP (z l start len : ℕ) : ℕ → ℕ
  | 0 => l
  | c + 1 => innerP z (bfP z l start len) (start + 1) len c

/-- Packed-natural middle loop (`numBlocks` blocks, zeta index `k`). -/
def middleP (l len startOff k : ℕ) : ℕ → ℕ × ℕ
  | 0 => (l, k)
  | nb + 1 =>
    let z := 17 ^ brN k % 3329
    middleP (innerP z l startOff len len) len (startOff + 2 * len) (k + 1) nb

/-- Packed-natural outer loop over the layer list. -/
def outerP (l k : ℕ) : List ℕ → ℕ × ℕ
  | [] => (l, k)
  | len :: rest =>
    let r := middleP l len 0 k (256 / (2 * len))
    outerP r.1 r.2 rest

/-- Packed-natural clone of `ntt` (Algorithm 7). -/
def nttP (l : ℕ) : ℕ := (outerP l 1 nttLens).1

/-- Packed standard basis vector `δⱼ`: digit `j` is `1`, all others `0`. -/
def deltaP (j : ℕ) : ℕ := 4096 ^ j

/-- Closed-form value of `NTT(δⱼ)` at index `idx` (a `ℕ` in `[0, 3329)`). -/
def formulaCell (j idx : ℕ) : ℕ :=
  if idx % 2 = j % 2 then 17 ^ ((2 * brN (idx / 2) + 1) * (j / 2)) % 3329 else 0

/-- The packed closed form of `NTT(δⱼ)`. -/
def formulaP (j : ℕ) : ℕ := packList ((List.range 256).map (formulaCell j))

/-! ### Packed-natural clone of Algorithm 8 (butterfly layers only)

The Gentleman–Sande butterfly `(a, b) ↦ (a + b, ζ·(b − a))`, the three loops
with the zeta index `k` threaded *downward* from 127, and no final scaling:
the kernel check compares the result against `128 · δⱼ`, and the `128⁻¹`
scaling is handled symbolically in `RoundTrip.lean`. -/

/-- Packed-natural inverse butterfly at positions `j` and `j + len`, twiddle `z`. -/
def ibfP (z l j len : ℕ) : ℕ :=
  let a := getP l j
  let b := getP l (j + len)
  setP (setP l (j + len) (z * ((b + 3329 - a) % 3329) % 3329)) j ((a + b) % 3329)

/-- Packed-natural inverse inner loop (`count` butterflies from `start`). -/
def iinnerP (z l start len : ℕ) : ℕ → ℕ
  | 0 => l
  | c + 1 => iinnerP z (ibfP z l start len) (start + 1) len c

/-- Packed-natural inverse middle loop (`numBlocks` blocks, zeta index `k` descending). -/
def imiddleP (l len startOff k : ℕ) : ℕ → ℕ × ℕ
  | 0 => (l, k)
  | nb + 1 =>
    let z := 17 ^ brN k % 3329
    imiddleP (iinnerP z l startOff len len) len (startOff + 2 * len) (k - 1) nb

/-- Packed-natural inverse outer loop over the layer list. -/
def iouterP (l k : ℕ) : List ℕ → ℕ × ℕ
  | [] => (l, k)
  | len :: rest =>
    let r := imiddleP l len 0 k (256 / (2 * len))
    iouterP r.1 r.2 rest

/-- Packed-natural clone of the butterfly layers of `invNtt` (Algorithm 8,
without the final `128⁻¹` scaling). -/
def invNttP (l : ℕ) : ℕ := (iouterP l 127 invNttLens).1

end Fips203
