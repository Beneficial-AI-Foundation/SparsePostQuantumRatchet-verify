/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Specs.Encoding.Gf.Reduce.ReduceFromByte
/-!
# Spec theorem for `spqr::encoding::gf::reduce::reduce_bytes`
-/

open Aeneas Aeneas.Std Result Polynomial spqr.math.gf

namespace spqr.encoding.gf.reduce

private lemma index_usize_set_ne
    {α : Type} {n : Usize}
    (v : Array α n) (i j : Usize) (x : α)
    (hne : Nat.not_eq i.val j.val) :
    Array.index_usize (v.set i x) j = Array.index_usize v j := by
  unfold Array.index_usize
  simp only [Array.getElem?_Usize_eq, Array.set_val_eq]
  congr 1; exact List.getElem?_set_ne (Nat.not_eq_imp_not_eq hne)

private lemma index_usize_set_eq_of_val_eq
    {α : Type} {n : Usize}
    (v : Array α n) (i j : Usize) (x : α)
    (hji : j.val = i.val) (hi : i.val < n.val) :
    Array.index_usize (v.set i x) j = ok x := by
  unfold Array.index_usize
  simp only [Array.getElem?_Usize_eq, Array.set_val_eq]
  rw [show i.val = j.val from hji.symm,
      List.getElem?_set_self (by have := Array.length_eq v; omega)]

/--
**Spec theorem for `spqr::encoding::gf::reduce::reduce_bytes` (loop)**

The loop maintains the invariant that all entries `out[j]` for `j < i` equal `reduceByteTable j`,
and upon completion (`i = 256`) the entire output array is correctly populated.
-/
@[step]
theorem reduce_bytes_loop_spec
    (out : Array U16 256#usize) (i : Usize)
    (hi : i.val ≤ 256)
    (h_inv : ∀ j : Usize, j.val < i.val →
      ∃ v : U16,
        Array.index_usize out j = ok v ∧
          v.val = reduceByteTable j.val) :
    reduce_bytes_loop out i ⦃ (result : Std.Array U16 256#usize) =>
      ∀ j : Usize, j.val < 256 →
        ∃ v : U16,
          Array.index_usize result j = ok v ∧
            v.val = reduceByteTable j.val ⦄ := by
  unfold reduce_bytes_loop
  apply loop.spec_decr_nat
    (measure := fun (p : (Array U16 256#usize) × Usize) => 256 - p.2.val)
    (inv := fun (p : (Array U16 256#usize) × Usize) =>
      p.2.val ≤ 256 ∧
      ∀ j : Usize, j.val < p.2.val →
        ∃ v : U16, Array.index_usize p.1 j = ok v ∧ v.val = reduceByteTable j.val)
  · intro ⟨out', i'⟩ ⟨hi'_bound, h_inv'⟩
    simp only []
    unfold reduce_bytes_loop.body
    by_cases hLt : i' < 256#usize
    · simp only [hLt]; step*
      refine ⟨by scalar_tac, fun j hj => ?_, by scalar_tac⟩
      by_cases hjne : j.val = i'.val
      · exact ⟨i3,
          by rw [a_post]; exact index_usize_set_eq_of_val_eq out' i' j _ hjne (by scalar_tac),
          by simp_all [UScalar.cast_val_eq]⟩
      · obtain ⟨v, hv_idx, hv_val⟩ := h_inv' j (by scalar_tac)
        exact ⟨v,
          by rw [a_post]; rw [index_usize_set_ne out' i' j _ (by scalar_tac)]; exact hv_idx,
          hv_val⟩
    · simp only [hLt]; exact fun j hj => h_inv' j (by scalar_tac)
  · exact ⟨hi, h_inv⟩

/--
**Spec theorem for `spqr::encoding::gf::reduce::reduce_bytes`**

Builds the 256-entry reduction lookup table: for every index `j < 256`, `result[j].val =
reduceByteTable j`.
-/
@[step]
theorem reduce_bytes_spec :
    reduce_bytes ⦃ (result : Std.Array U16 256#usize) =>
      ∀ j : Usize, j.val < 256 →
        ∃ v : U16,
          Array.index_usize result j = ok v ∧
            v.val = reduceByteTable j.val ⦄ := by
  unfold reduce_bytes
  apply WP.spec_mono (reduce_bytes_loop_spec _ 0#usize (by scalar_tac)
    (fun j hj => by scalar_tac))
  exact fun _ h => h

/-! ## Full-range polynomial correctness of the reduction table -/

/-- Combined high-to-low loop function tracking both `a` (byte) and `out` (accumulator). -/
private def reduceByteLoopFull (a out : Nat) : (n : Nat) → Nat × Nat
  | 0     => (a, out)
  | n + 1 =>
    if a.testBit n then
      let ps := 0x1100b <<< n
      reduceByteLoopFull ((a ^^^ (ps >>> 16)) % 256) (out ^^^ ps) n
    else
      reduceByteLoopFull a out n

private lemma reduceByteLoopFull_snd_eq (a out n : Nat) :
    (reduceByteLoopFull a out n).2 = reduceFromByteLoopSpec a out n := by
  induction n generalizing a out with
  | zero => rfl
  | succ n ih =>
    simp only [reduceByteLoopFull, reduceFromByteLoopSpec]
    split <;> exact ih _ _

private lemma xor_lt_256 (a b : Nat) (ha : a < 256) (hb : b < 256) : a ^^^ b < 256 := by
  have tb : ∀ x, x < 256 → ∀ j, 8 ≤ j → x.testBit j = false := fun x hx j hj =>
    Nat.testBit_eq_false_of_lt (calc x < 256 := hx
      _ = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj)
  apply Nat.lt_of_testBit 8
  · simp [Nat.testBit_xor, tb a ha 8 le_rfl, tb b hb 8 le_rfl]
  · decide
  · intro j hj
    simp [Nat.testBit_xor, tb a ha j (by omega), tb b hb j (by omega),
      Nat.testBit_eq_false_of_lt (show 256 < 2 ^ j from
        calc (256 : Nat) = 2 ^ 8 := by norm_num
          _ < 2 ^ j := Nat.pow_lt_pow_right (by norm_num) (by omega))]

private lemma reduceByteLoopFull_inv (a out : Nat) (n : Nat) (ha : a < 256) :
    (natToBinaryPoly ((reduceByteLoopFull a out n).2 % 2 ^ 16) +
     natToBinaryPoly (reduceByteLoopFull a out n).1 * X ^ 16) %ₘ polyGF2 =
    (natToBinaryPoly (out % 2 ^ 16) + natToBinaryPoly a * X ^ 16) %ₘ polyGF2 := by
  induction n generalizing a out with
  | zero => simp [reduceByteLoopFull]
  | succ n ih =>
    simp only [reduceByteLoopFull]
    split_ifs with htb
    · have hn_le : n ≤ 7 := by
        by_contra hlt; push_neg at hlt
        have := Nat.testBit_eq_false_of_lt (calc a < 256 := ha
          _ = 2 ^ 8 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega))
        simp_all
      set ps := 0x1100b <<< n with hps_def
      have hps_hi_lt : ps >>> 16 < 256 := by unfold ps; interval_cases n <;> decide
      have ha'_lt : a ^^^ (ps >>> 16) < 256 := xor_lt_256 a (ps >>> 16) ha hps_hi_lt
      have ha'_eq : (a ^^^ (ps >>> 16)) % 256 = a ^^^ (ps >>> 16) := Nat.mod_eq_of_lt ha'_lt
      have hmonic := polyGF2_monic
      have hpoly_ps : natToBinaryPoly ps = polyGF2 * X ^ n := by
        unfold ps; simp [natToBinaryPoly_shiftLeft, natToBinaryPoly_polyGF2]
      have hxor_mod : ∀ p q : Nat, (p ^^^ q) % 2 ^ 16 = p % 2 ^ 16 ^^^ q % 2 ^ 16 :=
        fun p q => Nat.eq_of_testBit_eq fun i => by
          simp only [Nat.testBit_xor, Nat.testBit_mod_two_pow]; by_cases hi : i < 16 <;> simp [hi]
      have hrw : natToBinaryPoly ((out ^^^ ps) % 2 ^ 16) +
                 natToBinaryPoly (a ^^^ ps >>> 16) * X ^ 16 =
                 (natToBinaryPoly (out % 2 ^ 16) + natToBinaryPoly a * X ^ 16) +
                 polyGF2 * X ^ n := by
        rw [hxor_mod, natToBinaryPoly_xor, natToBinaryPoly_xor, add_mul,
            ← hpoly_ps, natToBinaryPoly_split ps 16]
        ring
      simp only [ha'_eq]
      rw [ih _ _ ha'_lt, hrw, Polynomial.add_modByMonic,
          (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mpr (dvd_mul_right polyGF2 _), add_zero]
    · exact ih a out ha

private lemma reduceByteLoopFull_carry_zero (k : Nat) (hk : k < 256) :
    (reduceByteLoopFull k 0 8).1 = 0 := by
  have h : ∀ k' : Fin 256, (reduceByteLoopFull k'.val 0 8).1 = 0 := by decide
  exact h ⟨k, hk⟩

/--
**(a) Full-range table polynomial correctness (spec-level).**

For any byte value `k < 256`:
  `natToBinaryPoly (reduceByteTable k) = (natToBinaryPoly k * X ^ 16) %ₘ polyGF2`
-/
theorem reduceByteTable_eq_poly_full (k : Nat) (hk : k < 256) :
    natToBinaryPoly (reduceByteTable k) =
      (natToBinaryPoly k * X ^ 16) %ₘ polyGF2 := by
  unfold reduceByteTable
  rw [← reduceByteLoopFull_snd_eq]
  have hmonic := polyGF2_monic
  have hPOLYdeg := polyGF2_natDegree
  have hinv := reduceByteLoopFull_inv k 0 8 hk
  simp only [Nat.zero_mod, natToBinaryPoly_zero, zero_add] at hinv
  simp only [reduceByteLoopFull_carry_zero k hk, natToBinaryPoly_zero, zero_mul, add_zero] at hinv
  set A := natToBinaryPoly ((reduceByteLoopFull k 0 8).2 % 2 ^ 16)
  have hA_deg : A.natDegree < 16 := by
    rcases eq_or_ne A 0 with heq | hne; · simp [heq]
    rw [Polynomial.natDegree_lt_iff_degree_lt hne, Polynomial.degree_lt_iff_coeff_zero]
    intro m hm; simp only [A, natToBinaryPoly_coeff]
    exact if_neg (Bool.not_eq_true _ ▸ Nat.testBit_eq_false_of_lt
      (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (Nat.pow_le_pow_right (by norm_num) hm)))
  have hA_self : A %ₘ polyGF2 = A := by
    have hA_eq := Polynomial.modByMonic_add_div A hmonic
    suffices A /ₘ polyGF2 = 0 by rw [this, mul_zero, add_zero] at hA_eq; exact hA_eq
    by_contra hne
    have hprod_deg : (A /ₘ polyGF2 * polyGF2).natDegree ≥ 16 := by
      rw [Polynomial.natDegree_mul hne hmonic.ne_zero, hPOLYdeg]; omega
    have hmod_lt : (A %ₘ polyGF2).natDegree < 16 := by
      rw [← hPOLYdeg]; exact Polynomial.natDegree_modByMonic_lt A hmonic polyGF2_ne_one
    have hprod_ne : A /ₘ polyGF2 * polyGF2 ≠ 0 := fun h => by simp [h] at hprod_deg
    have hrearr : A = A %ₘ polyGF2 + A /ₘ polyGF2 * polyGF2 := by
      rw [mul_comm polyGF2] at hA_eq; exact hA_eq.symm
    have : A.natDegree ≥ 16 := by
      rw [hrearr]; exact le_trans hprod_deg (Polynomial.le_natDegree_of_ne_zero (by
        rw [Polynomial.coeff_add, Polynomial.coeff_eq_zero_of_natDegree_lt (by linarith), zero_add]
        exact Polynomial.leadingCoeff_ne_zero.mpr hprod_ne))
    linarith
  rwa [hA_self] at hinv

/--
**Spec theorem for `spqr::encoding::gf::reduce::reduce_bytes` (polynomial)**

GF(2)[X] polynomial correctness: for every index `j < 256`, the table entry satisfies
`natToBinaryPoly result[j].val = (natToBinaryPoly j * X^16) %ₘ polyGF2`.
-/
@[step]
theorem reduce_byte_spec_poly :
    reduce_bytes ⦃ (result : Std.Array U16 256#usize) =>
      ∀ j : Usize, j.val < 256 →
        ∃ v : U16,
          Array.index_usize result j = ok v ∧
            natToBinaryPoly v.val =
              (natToBinaryPoly j.val * X ^ 16) %ₘ polyGF2 ⦄ := by
  apply WP.spec_mono reduce_bytes_spec
  intro result hres j hj
  obtain ⟨v, hv_idx, hv_val⟩ := hres j hj
  exact ⟨v, hv_idx, by rw [hv_val]; exact reduceByteTable_eq_poly_full j.val hj⟩

end spqr.encoding.gf.reduce
