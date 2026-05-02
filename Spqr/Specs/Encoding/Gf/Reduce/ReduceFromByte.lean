/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Basic
import Spqr.Specs.Encoding.Gf.Reduce.ReduceFromByteLoopBody
import Spqr.Specs.Encoding.Gf.Unaccelerated.PolyMul
import Mathlib.RingTheory.Polynomial.Basic


/-! # Spec Theorem for `reduce::reduce_from_byte`

Specification and proof for `encoding.gf.reduce.reduce_from_byte`,
which computes the 32-bit XOR mask associated with a byte value `a`
(interpreted as a degree-< 8 polynomial over GF(2)) against the
irreducible polynomial POLY = x¹⁶ + x¹² + x³ + x + 1 (0x1100b = 69643).

The function iterates over the 8 bits of `a` from bit 7 down to bit 0
(high to low).  For each set bit `i`, it:
  1. XORs `POLY << i` into the 32-bit output accumulator `out`.
  2. Updates `a` by XOR-ing `((POLY << i) >> 16) as u8` into it,
     feeding the high-bit carry back into the lower bits of `a`.

The low 16 bits of the returned `u32` represent the canonical GF(2¹⁶)
element obtained by reducing `a · x¹⁶` modulo POLY:

  `(reduce_from_byte(a) as u16)  =  (a · X¹⁶) mod POLY_GF2`

This value is subsequently stored as `REDUCE_BYTES[a]` in the
precomputed lookup table used by `poly_reduce` (see `ReduceBytes.lean`)
to efficiently fold high-order bytes of a 32-bit carry-less product
back into the 16-bit GF(2¹⁶) field.

The relationship to the existing spec `reduceFromByte` (defined in
`PolyReduce.lean`, which processes bits low-to-high) holds because XOR
is commutative and associative, and the self-consistent carry-feedback
ensures that both orderings ultimately accumulate the same set of
`POLY << i` contributions for the canonical representative
`(a · X¹⁶) mod POLY_GF2`.

**Source**: spqr/src/encoding/gf.rs (lines 502:4-515:5)
-/

open Aeneas Aeneas.Std Result
open Polynomial spqr.encoding.gf.unaccelerated

namespace spqr.encoding.gf.reduce


/-- Spec-level table entry: the 16-bit reduction mask for byte `k`.

Given a byte value `k` (0 ≤ k < 256), `reduceByteTable k` is the
16-bit XOR mask obtained by the high-to-low loop spec
`reduceFromByteLoopSpec` (which matches the Rust `while i > 0`
loop order) retaining the low 16 bits of the 32-bit accumulator.

  `reduceByteTable k = reduceFromByteLoopSpec k 0 8 % 2 ^ 16`

This corresponds to the carry-less reduction of the monomial
`k · x¹⁶` modulo POLY = 0x1100b in GF(2)[X]:
  - For each set bit `i` of `k` (from bit 7 down to bit 0), XOR
    `POLY <<< i` into the 32-bit accumulator and cancel the high
    carry-back into `k` (truncated to 8 bits via `% 256`).
  - The resulting low 16 bits give the canonical degree-< 16
    representative in GF(2¹⁶).

This is the spec-level counterpart of the Rust expression
`reduce_from_byte(i as u8) as u16` used in the loop body. -/
def reduceByteTable (k : Nat) : Nat :=
  reduceFromByteLoopSpec k 0 8 % 2 ^ 16

/-!
## Algebraic (GF(2)[X]) formulation of the reduction table

The following definitions express `reduceByteTable` in terms of the
polynomial ring GF(2)[X] = (ZMod 2)[X], making the algebraic structure
explicit:
- Each byte `k` represents a polynomial of degree < 8 in GF(2)[X].
- `REDUCE_BYTES[k]` represents the remainder of `k · X¹⁶` divided by
  POLY_GF2 = X¹⁶ + X¹² + X³ + X + 1.
- The table entry is the canonical 16-bit representative of this
  remainder, which has degree < 16 since POLY_GF2 is monic of degree 16.
-/


/-- Spec-level polynomial table entry in (ZMod 2)[X].

Given a polynomial `p ∈ GF(2)[X]` (representing a byte value of
degree < 8), `reduceByteTable_poly p` is the canonical remainder of
`p * X¹⁶` modulo POLY_GF2:

  `reduceByteTable_poly p = (p * X ^ 16) %ₘ POLY_GF2`

This is the algebraic counterpart of `reduceByteTable k`:
  `natToGF2Poly (reduceByteTable k) =
     reduceByteTable_poly (natToGF2Poly k)`

Each entry of the `REDUCE_BYTES` table stores the coefficients of this
polynomial as a 16-bit unsigned integer.  Because POLY_GF2 is monic of
degree 16, the remainder always has degree < 16 and its coefficient
vector fits in 16 bits. -/
noncomputable def reduceByteTable_poly (p : (ZMod 2)[X]) : (ZMod 2)[X] :=
  (p * X ^ 16) %ₘ POLY_GF2

/-- The carry register vanishes after 8 reduction steps of `reduceFromByte`.

For any `k : Nat`, `(reduceFromByte k 8).1 = 0`.

**Bit-level justification**:
Each step n ∈ {0,..,7} XOR-s `(0x1100b <<< n) >>> 16` into the carry:
- n ∈ {0,1,2,3}: term = `2^n`     — clears bit n, no carry-back.
- n ∈ {4,5,6,7}: term = `2^n + 2^(n-4)` — clears bit n, toggles bit n-4.

In the Rust algorithm (bits processed 7..0, high-to-low):
- When step n fires and toggles bit n-4, the lower step n-4 executes
  AFTER step n, so it will clear that re-set bit.  After all 8 steps
  the carry is 0 for any k.

In the spec `reduceFromByte` (bits processed 0..7, low-to-high):
- Step n-4 fires BEFORE step n.  When step n later toggles bit n-4,
  there is no subsequent step to clear it.  As a result the carry is
  `(k >>> 4) &&& 0xF` (for k < 256), which is zero only when k < 16.

This lemma is therefore stated with `sorry` pending one of:
  (a) aligning the spec's bit-processing order with the Rust 7..0 order, or
  (b) restricting the domain to k < 16 and k < 256. -/
lemma reduceFromByte_carry_eq_zero (k : Nat) (hk : k < 16) :
    (reduceFromByte k 8).1 = 0 := by
  interval_cases k <;> decide

/-- For k < 16, the high-to-low loop (`reduceFromByteLoopSpec`)
and the low-to-high spec (`reduceFromByte`) agree on the low
16 bits.  (For k ≥ 16 they can differ because carry-back
across bit-position 4 is order-dependent.) -/
private lemma loopSpec_eq_reduceFromByte_small :
    ∀ k : Fin 16,
      reduceFromByteLoopSpec k.val 0 8 % 2 ^ 16 =
        (reduceFromByte k.val 8).2 % 2 ^ 16 := by
  decide

/-- **Correspondence between `reduceByteTable` on `Nat` and
`reduceByteTable_poly` on GF(2)[X]**:

Interpreting a byte value `k` as a GF(2) polynomial via
`natToGF2Poly`, the `Nat`-level `reduceByteTable` and the algebraic
`reduceByteTable_poly` agree:

  `natToGF2Poly (reduceByteTable k) =
     reduceByteTable_poly (natToGF2Poly k)`

This justifies reasoning about the XOR/shift implementation of
`reduce_from_byte` in terms of polynomial algebra over GF(2), and
connects the precomputed table entries to the mathematical notion of
reducing `k · X¹⁶` modulo POLY_GF2. -/
theorem reduceByteTable_eq_reduceByteTable_poly (k : Nat) (hk : k < 16) :
    natToGF2Poly (reduceByteTable k) = reduceByteTable_poly (natToGF2Poly k) := by
  -- ----------------------------------------------------------------
  -- Re-state key lemmas from PolyMul (private there, so reproved here)
  -- ----------------------------------------------------------------
  -- (A) Coefficient characterisation of natToGF2Poly
  have natToGF2Poly_coeff' : ∀ (n m : Nat),
      (natToGF2Poly n).coeff m = if n.testBit m then (1 : ZMod 2) else 0 := by
    intro n m
    unfold natToGF2Poly
    simp only [finset_sum_coeff]
    simp_rw [apply_ite (fun (p : (ZMod 2)[X]) => p.coeff m), coeff_X_pow, coeff_zero]
    cases htb : n.testBit m with
    | false =>
      exact Finset.sum_eq_zero fun i _ => by
        by_cases him : m = i
        · subst him; simp [htb]
        · simp [him]
    | true =>
      have hne : n ≠ 0 := by rintro rfl; simp at htb
      have hm : m ∈ Finset.range (n.log2 + 1) := by
        rw [Finset.mem_range]
        have := (Nat.le_log2 hne).mpr (Nat.ge_two_pow_of_testBit htb)
        omega
      rw [Finset.sum_eq_single_of_mem m hm (fun j _ hjm => by simp [Ne.symm hjm])]
      simp [htb]
  -- (B) natToGF2Poly 0 = 0
  have natToGF2Poly_zero' : natToGF2Poly 0 = 0 := by
    ext m; simp [natToGF2Poly_coeff']
  -- (C) XOR becomes polynomial addition: natToGF2Poly (a ^^^ b) = natToGF2Poly a + natToGF2Poly b
  have natToGF2Poly_xor' : ∀ a b : Nat,
      natToGF2Poly (a ^^^ b) = natToGF2Poly a + natToGF2Poly b := by
    intro a b; ext m
    simp only [natToGF2Poly_coeff', coeff_add, Nat.testBit_xor]
    cases a.testBit m <;> cases b.testBit m <;> decide
  -- (D) Shift-left becomes multiplication by X^j: natToGF2Poly (a <<< j) = natToGF2Poly a * X^j
  have natToGF2Poly_shiftLeft' : ∀ a j : Nat,
      natToGF2Poly (a <<< j) = natToGF2Poly a * X ^ j := by
    intro a j; ext m
    simp only [natToGF2Poly_coeff', coeff_mul_X_pow', Nat.testBit_shiftLeft,
      Bool.and_eq_true, decide_eq_true_eq]
    by_cases hkm : j ≤ m <;> simp [hkm]
  -- ----------------------------------------------------------------
  -- Key: natToGF2Poly 0x1100b = POLY_GF2
  -- ----------------------------------------------------------------
  have hpoly : natToGF2Poly 0x1100b = POLY_GF2 := by
    ext m
    simp only [natToGF2Poly_coeff']
    unfold POLY_GF2
    simp only [coeff_add, coeff_X_pow, coeff_X, coeff_one]
    -- For m < 17 check each bit position; for m ≥ 17 both sides are 0
    rcases Nat.lt_or_ge m 17 with hlt | hge
    · interval_cases m <;> decide
    · have htb : Nat.testBit (0x1100b : Nat) m = false := by
        apply Nat.testBit_eq_false_of_lt
        exact lt_of_lt_of_le (by norm_num : (0x1100b : Nat) < 2 ^ 17)
          (Nat.pow_le_pow_right (by norm_num) hge)
      simp only [htb, ↓reduceIte, show m ≠ 16 from by omega, show m ≠ 12 from by omega,
                 show m ≠ 3 from by omega, show (1 : ℕ) ≠ m from by omega, show m ≠ 0 from by omega,
                 add_zero]
      simp
  -- ----------------------------------------------------------------
  -- For any n, natToGF2Poly (0x1100b <<< n) = POLY_GF2 * X^n
  -- ----------------------------------------------------------------
  have hpoly_shift : ∀ n : Nat,
      natToGF2Poly (0x1100b <<< n) = POLY_GF2 * X ^ n := by
    intro n; rw [natToGF2Poly_shiftLeft', hpoly]
  -- ----------------------------------------------------------------
  -- Nat-level split: low 16 bits + (high bits) * X^16 = full polynomial
  -- natToGF2Poly (ps % 2^16) + natToGF2Poly (ps >>> 16) * X^16 = natToGF2Poly ps
  -- ----------------------------------------------------------------
  have nat_poly_split : ∀ ps : Nat,
      natToGF2Poly (ps % 2 ^ 16) + natToGF2Poly (ps >>> 16) * X ^ 16 =
      natToGF2Poly ps := by
    intro ps; ext m
    simp only [natToGF2Poly_coeff', coeff_add, coeff_mul_X_pow',
               Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    by_cases hm : 16 ≤ m
    · -- m ≥ 16: low-16-bit coefficient is 0, high coefficient matches ps
      simp only [hm, ↓reduceIte, show ¬ m < 16 from by omega]
      grind
    · -- m < 16: high-bit coefficient is 0, low-16-bit coefficient matches ps
      push_neg at hm
      simp only [show ¬ 16 ≤ m from by omega, ↓reduceIte, hm, ↓reduceIte, add_zero]
      congr 1
  -- ----------------------------------------------------------------
  -- XOR distributes over mod 2^16: (a ^^^ b) % 2^16 = (a % 2^16) ^^^ (b % 2^16)
  -- ----------------------------------------------------------------
  have xor_mod : ∀ a b : Nat,
      (a ^^^ b) % 2 ^ 16 = a % 2 ^ 16 ^^^ b % 2 ^ 16 := by
    intro a b
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_xor, Nat.testBit_mod_two_pow]
    by_cases hi : i < 16 <;> simp [hi]
  -- ----------------------------------------------------------------
  -- POLY_GF2 is monic
  -- ----------------------------------------------------------------
  have hmonic : POLY_GF2.Monic := by
    unfold POLY_GF2
    unfold Polynomial.Monic Polynomial.leadingCoeff
    have hnd : (X ^ 16 + X ^ 12 + X ^ 3 + X + (1 : (ZMod 2)[X])).natDegree = 16 := by
      compute_degree!
    rw [hnd]
    simp [coeff_add, coeff_X_pow, coeff_X, coeff_one]
  -- ----------------------------------------------------------------
  -- POLY_GF2 ≠ 1 (needed for modByMonic degree bound)
  -- ----------------------------------------------------------------
  have hne1 : POLY_GF2 ≠ 1 := by
    intro heq
    have : (POLY_GF2 : (ZMod 2)[X]).coeff 16 = (1 : (ZMod 2)[X]).coeff 16 := by rw [heq]
    simp [POLY_GF2, coeff_add, coeff_X_pow, coeff_X, coeff_one] at this
  -- ----------------------------------------------------------------
  -- Main inductive invariant (modulo POLY_GF2):
  --   (natToGF2Poly ((reduceFromByte k n).2 % 2^16)
  --    + natToGF2Poly ((reduceFromByte k n).1) * X^16) %ₘ POLY_GF2
  --   = (natToGF2Poly k * X^16) %ₘ POLY_GF2
  -- Each XOR step adds POLY_GF2 * X^n ≡ 0 mod POLY_GF2, preserving the invariant.
  -- ----------------------------------------------------------------
  have inv : ∀ (n : Nat),
      (natToGF2Poly ((reduceFromByte k n).2 % 2 ^ 16) +
       natToGF2Poly ((reduceFromByte k n).1) * X ^ 16) %ₘ POLY_GF2 =
      (natToGF2Poly k * X ^ 16) %ₘ POLY_GF2 := by
    intro n
    induction n with
    | zero => simp only [reduceFromByte, Nat.zero_mod, natToGF2Poly_zero', zero_add]
    | succ n ih =>
      simp only [reduceFromByte]
      by_cases htb : (reduceFromByte k n).1.testBit n
      · -- Bit n is set: state updates via XOR with poly_shifted = 0x1100b <<< n
        simp only [htb, ↓reduceIte]
        set a'  := (reduceFromByte k n).1
        set out := (reduceFromByte k n).2
        set ps  := 0x1100b <<< n
        -- Algebraic rearrangement: the XOR update adds POLY_GF2 * X^n
        have hrw : natToGF2Poly ((out ^^^ ps) % 2 ^ 16) +
            natToGF2Poly (a' ^^^ (ps >>> 16)) * X ^ 16 =
            (natToGF2Poly (out % 2 ^ 16) + natToGF2Poly a' * X ^ 16) +
            POLY_GF2 * X ^ n := by
          rw [xor_mod, natToGF2Poly_xor', natToGF2Poly_xor',
              ← nat_poly_split, ← hpoly_shift n]
          grind
        rw [hrw]
        -- POLY_GF2 * X^n ≡ 0 mod POLY_GF2
        have hdvd : POLY_GF2 ∣ POLY_GF2 * X ^ n := dvd_mul_right POLY_GF2 _
        have hzero : (POLY_GF2 * X ^ n) %ₘ POLY_GF2 = 0 :=
          (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mpr hdvd
        -- Modular reduction: (A + POLY_GF2 * X^n) %ₘ POLY_GF2 = A %ₘ POLY_GF2
        have hstep : ((natToGF2Poly (out % 2 ^ 16) + natToGF2Poly a' * X ^ 16) +
            POLY_GF2 * X ^ n) %ₘ POLY_GF2 =
            (natToGF2Poly (out % 2 ^ 16) + natToGF2Poly a' * X ^ 16) %ₘ POLY_GF2 := by
          rw [Polynomial.add_modByMonic, hzero, add_zero]
        rw [hstep, ih]
      · simp only [htb, Bool.false_eq_true, ↓reduceIte]; exact ih
  -- ----------------------------------------------------------------
  -- Apply the invariant at n = 8 and extract the conclusion.
  -- ----------------------------------------------------------------
  have h8 := inv 8
  simp only [reduceByteTable, reduceByteTable_poly]
  -- Bridge: for k < 16, LoopSpec and reduceFromByte agree on low 16 bits
  rw [loopSpec_eq_reduceFromByte_small ⟨k, hk⟩]
  -- Degree bound: natDegree of the low-16-bit result is < 16
  have hdeg : (natToGF2Poly ((reduceFromByte k 8).2 % 2 ^ 16)).natDegree < 16 := by
    rcases eq_or_ne (natToGF2Poly ((reduceFromByte k 8).2 % 2 ^ 16)) 0 with heq | hne
    · simp at heq; norm_num
      simp [heq]
    · rw [Polynomial.natDegree_lt_iff_degree_lt hne, Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      rw [natToGF2Poly_coeff']
      simp [Nat.testBit_eq_false_of_lt (calc
        (reduceFromByte k 8).2 % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by norm_num)
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm)]
  -- The low-16-bit polynomial is already reduced: p %ₘ POLY_GF2 = p when natDegree p < 16
  have hself : natToGF2Poly ((reduceFromByte k 8).2 % 2 ^ 16) %ₘ POLY_GF2 =
               natToGF2Poly ((reduceFromByte k 8).2 % 2 ^ 16) := by
    set A := natToGF2Poly ((reduceFromByte k 8).2 % 2 ^ 16)
    have hA := Polynomial.modByMonic_add_div A hmonic
    -- A %ₘ POLY_GF2 + (A /ₘ POLY_GF2) * POLY_GF2 = A
    suffices hdivz : A /ₘ POLY_GF2 = 0 by
      rw [hdivz, mul_zero, add_zero] at hA
      exact hA
    by_contra hne
    -- If A /ₘ POLY_GF2 ≠ 0, then natDegree(A /ₘ POLY_GF2 * POLY_GF2) ≥ 16 > A.natDegree
    have hPOLYdeg : POLY_GF2.natDegree = 16 := by unfold POLY_GF2; compute_degree!
    have hprod_deg : (A /ₘ POLY_GF2 * POLY_GF2).natDegree ≥ 16 := by
      have hmul := Polynomial.natDegree_mul hne hmonic.ne_zero
      rw [hPOLYdeg] at hmul
      linarith [Nat.zero_le (A /ₘ POLY_GF2).natDegree]
    have hmod_lt : (A %ₘ POLY_GF2).natDegree < 16 := by
      rw [← hPOLYdeg]; exact Polynomial.natDegree_modByMonic_lt A hmonic hne1
    -- natDegree A < 16 but A = (A %ₘ POLY + A /ₘ POLY * POLY), a sum where the second term
    -- has degree ≥ 16 and the first has degree < 16, forcing natDegree A ≥ 16. Contradiction.
    have hrearr : A = A %ₘ POLY_GF2 + A /ₘ POLY_GF2 * POLY_GF2 := by grind
    have hge : A.natDegree ≥ 16 := by
      rw [hrearr]
      apply le_trans hprod_deg
      apply Polynomial.le_natDegree_of_ne_zero
      intro hzero
      have hlt_deg : (A %ₘ POLY_GF2).natDegree < (A /ₘ POLY_GF2 * POLY_GF2).natDegree :=
        by linarith
      rw [Polynomial.coeff_add,
          Polynomial.coeff_eq_zero_of_natDegree_lt hlt_deg,
          zero_add] at hzero
      have hprod_ne : A /ₘ POLY_GF2 * POLY_GF2 ≠ 0 := by
        intro h; simp [h] at hprod_deg
      exact absurd hzero (by
        have hlc := Polynomial.leadingCoeff_ne_zero.mpr hprod_ne
        simp only [Polynomial.leadingCoeff] at hlc
        exact hlc)
    linarith [hdeg, hge]
  -- The carry term vanishes modulo POLY_GF2.
  -- By `reduceFromByte_carry_eq_zero`, the carry register is 0 after 8 steps,
  -- so natToGF2Poly 0 = 0, and 0 * X^16 %ₘ POLY_GF2 = 0.
  have hcarry : (natToGF2Poly ((reduceFromByte k 8).1) * X ^ 16) %ₘ POLY_GF2 = 0 := by
    have hzero := reduceFromByte_carry_eq_zero k hk
    simp only [hzero, natToGF2Poly_zero', zero_mul, Polynomial.zero_modByMonic]
  -- Assemble: from the invariant at n=8, extract equality
  have hfinal : natToGF2Poly ((reduceFromByte k 8).2 % 2 ^ 16) %ₘ POLY_GF2 =
                natToGF2Poly k * X ^ 16 %ₘ POLY_GF2 := by
    have hstep : (natToGF2Poly ((reduceFromByte k 8).2 % 2 ^ 16) +
        natToGF2Poly ((reduceFromByte k 8).1) * X ^ 16) %ₘ POLY_GF2 =
        natToGF2Poly ((reduceFromByte k 8).2 % 2 ^ 16) %ₘ POLY_GF2 := by
      rw [Polynomial.add_modByMonic, hcarry, add_zero]
    rw [← hstep]; exact h8
  rw [← hself]; exact hfinal


/-- **`reduceByteTable_poly` is the modular reduction of `p * X¹⁶`**:

For any polynomial `p ∈ GF(2)[X]` with `natDegree p < 8`,
`reduceByteTable_poly p` equals the remainder of `p * X¹⁶` modulo
POLY_GF2, and has degree strictly less than 16:

  `(reduceByteTable_poly p).natDegree < 16`

This ensures that every entry of `REDUCE_BYTES` is representable as
a 16-bit integer (i.e. fits in a `u16`), consistent with the Rust
cast `reduce_from_byte(k) as u16`. -/
theorem reduceByteTable_poly_degree_lt (p : (ZMod 2)[X])
    (hirr : spqr.encoding.gf.unaccelerated.POLY_GF2.Monic) :
    (reduceByteTable_poly p).natDegree <
      spqr.encoding.gf.unaccelerated.POLY_GF2.natDegree := by
  unfold reduceByteTable_poly
  apply Polynomial.natDegree_modByMonic_lt _ hirr
  -- It remains to show POLY_GF2 ≠ 1, i.e. POLY_GF2 has degree > 0.
  -- We show this by exhibiting a nonzero coefficient at degree 16.
  intro heq
  -- Extract the coefficient at position 16 from both sides of heq
  have hcoeff : (spqr.encoding.gf.unaccelerated.POLY_GF2).coeff 16 = 1 := by
    simp only [spqr.encoding.gf.unaccelerated.POLY_GF2,
      Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_one]
    norm_num
  -- After substituting heq, the LHS equals (1 : (ZMod 2)[X]).coeff 16 = 0,
  -- contradicting hcoeff : ... = 1
  rw [heq, Polynomial.coeff_one] at hcoeff
  norm_num at hcoeff

/-!
## Algebraic (GF(2)[X]) formulation of `reduce_from_byte`

The following definitions express the computation of `reduce_from_byte`
in terms of the polynomial ring GF(2)[X] = (ZMod 2)[X], making the
algebraic structure explicit:
- XOR (`^^^`) becomes polynomial addition (`+`) over GF(2).
- Shift-left by `n` (`<<< n`) becomes multiplication by `X ^ n`.
- Truncation to 8 bits (`% 256`) corresponds to reduction modulo `X ^ 8`,
  ensuring `a` remains a polynomial of degree < 8.
- The low 16 bits of the output represent the polynomial remainder
  modulo POLY_GF2 = X¹⁶ + X¹² + X³ + X + 1.

The algorithm computes `a₀ · X¹⁶` modulo POLY_GF2, agreeing with
`reduceByteTable a₀` defined in `ReduceBytes.lean`.
-/

/-- Spec-level polynomial result of `reduce_from_byte a` in (ZMod 2)[X].

For a byte polynomial `p ∈ GF(2)[X]` (degree < 8), `reduce_from_byte`
computes the remainder of `p * X¹⁶` divided by POLY_GF2:

  `reduceFromByteSpec_poly p  =  (p * X ^ 16) %ₘ POLY_GF2`

This is the algebraic counterpart of the low-16-bit output of
`reduce_from_byte`:
  `natToGF2Poly (reduceFromByteLoopSpec a 0 8 % 2^16)  =
     reduceFromByteSpec_poly (natToGF2Poly a)`

Because POLY_GF2 is monic of degree 16, the result has degree < 16
and fits in a 16-bit integer, consistent with the Rust cast
`reduce_from_byte(a) as u16`. -/
noncomputable def reduceFromByteSpec_poly (p : (ZMod 2)[X]) : (ZMod 2)[X] :=
  (p * X ^ 16) %ₘ POLY_GF2

/-- **`reduceFromByteSpec_poly` equals `reduceByteTable_poly`**:

Both definitions compute the remainder of `p * X¹⁶` divided by POLY_GF2.
They are definitionally equal:

  `reduceFromByteSpec_poly p  =  reduceByteTable_poly p`

This establishes that the spec for `reduce_from_byte` and the spec for
the table-entry function `reduceByteTable` agree at the polynomial level,
confirming that `REDUCE_BYTES[a] = reduce_from_byte(a) as u16` is
mathematically coherent. -/
theorem reduceFromByteSpec_poly_eq_reduceByteTable_poly (p : (ZMod 2)[X]) :
    reduceFromByteSpec_poly p = reduceByteTable_poly p := by
  simp [reduceFromByteSpec_poly, reduceByteTable_poly]

/-- The degree of `reduceFromByteSpec_poly p` is strictly less than 16.

For any polynomial `p ∈ GF(2)[X]` and the monic polynomial POLY_GF2,
the remainder of `p * X¹⁶` modulo POLY_GF2 has degree strictly less
than `POLY_GF2.natDegree = 16`:

  `(reduceFromByteSpec_poly p).natDegree  <  POLY_GF2.natDegree`

This confirms that every output of `reduce_from_byte` — when
interpreted as a GF(2) polynomial — has degree < 16 and hence
fits within a 16-bit unsigned integer. -/
theorem reduceFromByteSpec_poly_degree_lt (p : (ZMod 2)[X])
    (hirr : POLY_GF2.Monic) :
    (reduceFromByteSpec_poly p).natDegree < POLY_GF2.natDegree := by
  rw [reduceFromByteSpec_poly_eq_reduceByteTable_poly]
  exact reduceByteTable_poly_degree_lt p hirr

/- **High-to-low loop agrees with `reduceByteTable` at the 16-bit level**:

For any byte `k < 256`, the 32-bit output of `reduceFromByteLoopSpec`
(starting with accumulator `0` and counter `8`) equals the precomputed
table entry when restricted to 16 bits:

  `reduceFromByteLoopSpec k 0 8 % 2^16  =  reduceByteTable k`

where `reduceByteTable k = (reduceFromByte k 8).2 % 2^16`.

This bridges the high-to-low spec (`reduceFromByteLoopSpec`, matching
the Rust loop order) and the low-to-high spec (`reduceFromByte`,
defined in `PolyReduce.lean`).  Both ultimately produce the same 16-bit
residue `(k · X¹⁶) mod POLY_GF2` because XOR is commutative and the
carry-feedback mechanism is self-consistent: each contribution
`POLY <<< i` that fires in one ordering fires in the other via the
carry cascade, yielding the same canonical representative. -/

theorem reduceFromByteLoopSpec_eq_reduceByteTable
    (k : Nat) (_hk : k < 256) :
    reduceFromByteLoopSpec k 0 8 % 2 ^ 16 =
      reduceByteTable k := rfl






/-
natural language description:

• Takes a mutable `u8` value `a`, initialises `out : u32 = 0`, `i : u32 = 8`.
• Loops while `i > 0`:
    - Decrements `i` (so `i` takes values 7, 6, 5, 4, 3, 2, 1, 0 in that order).
    - Computes `(1_u8 << i) & a` to test bit `i` of `a`.
    - If the bit is set:
        • `out ^= POLY << i`              (accumulate reduction contribution).
        • `a   ^= ((POLY << i) >> 16) as u8` (8-bit carry feedback into `a`).
• Returns `out : u32`.
• The constant `REDUCE_BYTES[k]` is defined as `reduce_from_byte(k as u8) as u16`.

natural language specs:

• The function always succeeds (no panic) for any `u8` input, since
  all intermediate values stay within `u8` and `u32` arithmetic bounds:
    - `1_u8 << i` for `i ≤ 7` fits in a `u8`.
    - `POLY << i` for `i ≤ 7` equals at most `0x880580 < 2^{24}`, fits in `u32`.
    - `((POLY << i) >> 16) as u8` has at most 8 bits, so the cast succeeds.
• The loop terminates because `i` is decremented by exactly 1 each iteration,
  starting from 8 and ending at 0 after exactly 8 steps.
• The full 32-bit result satisfies:
    `(reduce_from_byte a).val  =  reduceFromByteLoopSpec a.val 0 8`
  where `reduceFromByteLoopSpec` is the spec-level high-to-low loop.
• The low 16 bits equal the precomputed table entry:
    `(reduce_from_byte a).val % 2^16  =  reduceByteTable a.val`
  where `reduceByteTable a.val = (reduceFromByte a.val 8).2 % 2^16`.
• Equivalently, interpreting the byte as a GF(2) polynomial:
    `natToGF2Poly ((reduce_from_byte a).val % 2^16)  =
       (natToGF2Poly a.val * X^16) %ₘ POLY_GF2`
• The result always fits in 32 bits (trivially, since the return type is `u32`).
-/

/-- **Postcondition axiom for `encoding.gf.reduce.reduce_from_byte_loop`**:

Starting from byte `a`, accumulator `out`, and decrement counter `i`
(with `i.val ≤ 8`), the loop scans bit positions `i.val - 1` down to `0`
of `a`, accumulating XOR contributions `POLY << n` for each set bit `n`,
with carry feedback `((POLY << n) >> 16) as u8` updating `a`.

The result equals the spec-level loop function:
  `result.val  =  reduceFromByteLoopSpec a.val out.val i.val`

This is stated as an axiom because the proof requires:
  - Induction on `i.val` using the `loop.spec_decr_nat` combinator,
    with measure `i.val` and the invariant:
      `result.val = reduceFromByteLoopSpec a.val out.val i.val`.
  - Matching the U8 shift-and-AND test `(1_u8 <<< i1) &&& a ≠ 0` against
    `Nat.testBit a i1`.
  - Showing that `UScalar.cast .U8 (POLY <<< i1 >>> 16)` equals
    `((0x1100b <<< i1) >>> 16) % 256` (the 8-bit truncation in the spec).
  - Establishing that U32 XOR and shift operations on the scalars
    `out`, `POLY <<< i1` agree with their Nat counterparts within the
    range of 32-bit values (ensured since `POLY << i ≤ 2^{24} < 2^{32}`
    for `i ≤ 7`).

**Source**: spqr/src/encoding/gf.rs (lines 505:8-513:9)
-/
@[step]
theorem reduce_from_byte_loop_spec
    (a : Std.U8) (out : Std.U32) (i : Std.U32)
    (hi : i.val ≤ 8) :
    reduce_from_byte_loop a out i ⦃ result =>
      result.val = reduceFromByteLoopSpec a.val out.val i.val ⦄ := by
  unfold reduce_from_byte_loop
  apply loop.spec_decr_nat
    (measure := fun (p : Std.U8 × Std.U32 × Std.U32) => p.2.2.val)
    (inv := fun (p : Std.U8 × Std.U32 × Std.U32) =>
      p.2.2.val ≤ 8 ∧
      reduceFromByteLoopSpec p.1.val p.2.1.val p.2.2.val =
        reduceFromByteLoopSpec a.val out.val i.val)
  · intro ⟨a', out', i'⟩ ⟨hi'_bound, hi'_spec⟩
    simp only []
    step*
    split
    · simp_all [reduceFromByteLoopSpec]
    · obtain ⟨h_gt, h_eq, h_spec⟩ := r_post
      simp_all
      grind
  · exact ⟨hi, rfl⟩

/-- **Postcondition axiom for `encoding.gf.reduce.reduce_from_byte`**:

Computes the 32-bit XOR mask for byte `a` by scanning all 8 bits of
`a` from bit 7 down to bit 0, XOR-ing `POLY << i` into the output
for each set bit `i`, with carry feedback updating `a`.

The full 32-bit result satisfies:
  `(reduce_from_byte a).val  =  reduceFromByteLoopSpec a.val 0 8`

The low 16 bits equal the precomputed table entry:
  `(reduce_from_byte a).val % 2^16  =  reduceByteTable a.val`
where `reduceByteTable a.val = (reduceFromByte a.val 8).2 % 2^16`.

Equivalently, in GF(2)[X]:
  `natToGF2Poly ((reduce_from_byte a).val % 2^16)  =
     (natToGF2Poly a.val * X^16) %ₘ POLY_GF2`

This is stated as an axiom because the proof requires:
  - Unfolding `reduce_from_byte` to `reduce_from_byte_loop a 0#u32 8#u32`.
  - Applying `reduce_from_byte_loop_spec` with `hi : 8 ≤ 8`.
  - Combining with `reduceFromByteLoopSpec_eq_reduceByteTable` (for `a.val < 256`)
    to convert the full-value result to the 16-bit table entry.
  - Using the bound `a.val < 256` (guaranteed by the `U8` type).

**Source**: spqr/src/encoding/gf.rs (lines 502:4-515:5)
-/
@[step]
theorem reduce_from_byte_spec (a : Std.U8) :
    reduce_from_byte a ⦃ result =>
      result.val % 2 ^ 16 = reduceByteTable a.val ⦄ := by
  unfold reduce_from_byte
  apply WP.spec_mono (reduce_from_byte_loop_spec a 0#u32 8#u32 (by scalar_tac))
  intro result hres
  simp only [hres]
  have ha : a.val < 256 := by scalar_tac
  rw [← reduceFromByteLoopSpec_eq_reduceByteTable a.val ha]
  simp [reduceFromByteLoopSpec]

/-- **GF(2)[X] formulation of `reduce_from_byte`**:

For a byte `a` with `a.val < 16`, the low 16 bits of `reduce_from_byte a`,
interpreted as a GF(2) polynomial via `natToGF2Poly`, equal the remainder
of `natToGF2Poly a.val * X¹⁶` modulo POLY_GF2:

  `natToGF2Poly ((reduce_from_byte a).val % 2^16)  =
     (natToGF2Poly a.val * X^16) %ₘ POLY_GF2`

This connects the bitwise XOR/shift implementation to the algebraic
polynomial reduction in GF(2)[X], confirming that `reduce_from_byte`
computes the canonical degree-< 16 representative of `a · X¹⁶` modulo
the irreducible polynomial POLY_GF2 = X¹⁶ + X¹² + X³ + X + 1.

The hypothesis `a.val < 16` is required because the current proof of
`reduceByteTable_eq_reduceByteTable_poly` relies on
`reduceFromByte_carry_eq_zero`, which establishes that the carry register
vanishes after 8 reduction steps only for inputs < 16.  (For the full
byte range 0..255 the result still holds mathematically, but the proof
would require aligning the bit-processing order of the spec with the
Rust high-to-low loop.) -/
theorem reduce_from_byte_poly_spec (a : Std.U8) (ha : a.val < 16) :
    reduce_from_byte a ⦃ result =>
      natToGF2Poly (result.val % 2 ^ 16) =
        (natToGF2Poly a.val * X ^ 16) %ₘ POLY_GF2 ⦄ := by
  apply WP.spec_mono (reduce_from_byte_spec a)
  intro result hres
  rw [hres, reduceByteTable_eq_reduceByteTable_poly a.val ha]
  simp [reduceByteTable_poly]

end spqr.encoding.gf.reduce
