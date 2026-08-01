/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Aeneas.GF16New
import Spqr.Specs.Aeneas.RangeIteratorNext
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.NecessaryPoints
import Spqr.Specs.Encoding.Polynomial.Pt.Cmp
import Spqr.Math.Poly.Aeneas.PolyIdentity
import Spqr.Math.Poly.Identities.Basic
import Spqr.Math.Poly.Identities.MultXdiff
import Spqr.Math.Poly.Lagrange.BasisPoly

/-!
# Spec theorem for `spqr::encoding::polynomial::PolyDecoder::add_chunk` — loop body 0

Each iteration of the `add_chunk` loop body constructs an evaluation point from a two-byte pair
in the chunk data and inserts it into the appropriate polynomial's sorted point set.  The point's
x-coordinate is derived from the chunk index (evaluation point index) and the y-coordinate is the
big-endian encoding of two consecutive data bytes into a GF(2¹⁶) element.

The iteration index `i` determines which of the 16 polynomials receives the point via the routing
`(chunk_index * 16 + i) % 16 = i`, and the x-coordinate is assigned as
`(chunk_index * 16 + i) / 16 = chunk_index`.  When all chunks have been processed, each polynomial
holds points with x-coordinates `0, 1, …, n−1`, which is exactly the `completePoints` format
required by `from_complete_points` for Lagrange interpolation over GF(2¹⁶).

A helper lemma establishes the key connection to the Lagrange polynomial identity framework:
polynomial routing (`chunk_point_routing`).
The downstream identities — Horner-scheme factorisation (`poly_identity_from`), template polynomial
construction (`mult_xdiff_result_eq`), and basis degree bounds (`natDegree_lagrangeBasisPoly_le`) —
are proved separately in the interpolation modules where the complete point list is available.

**Source**: spqr/src/encoding/polynomial.rs (lines 879:4–904:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

private instance instInhabitedSortedSetPt : Inhabited (sorted_vec.SortedSet Pt) :=
  ⟨alloc.vec.Vec.new Pt⟩

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop

/-- **Sorted insert totality**: `sortedInsert` always succeeds for any list, element, and starting
index, returning a triple of the insertion index, an optional replaced element, and the new list.

• The proof proceeds by induction on the list, case-splitting on the comparison result at each
  element.
• This totality guarantee is required by the `body_spec_0` proof to discharge the `sortedInsert`
  branch without a `fail` case. -/
private theorem sortedInsert_always_ok (list : List Pt) (x : Pt) (i : Nat) :
    ∃ idx opt newList,
      sorted_vec.SortedSet.sortedInsert Pt.Insts.CoreCmpOrd list x i =
      ok (idx, opt, newList) := by
  induction list generalizing i with
  | nil => exact ⟨i, none, [x], rfl⟩
  | cons a rest ih =>
    simp only [sorted_vec.SortedSet.sortedInsert]
    have h_cmp := Pt.Insts.CoreCmpOrd.cmp_spec a x
    rcases h_eq : Pt.Insts.CoreCmpOrd.cmp a x with ord | e | _
    · simp only [bind_tc_ok]
      rcases ord with _ | _ | _
      · simp only []
        obtain ⟨idx', opt', newList', h_rec⟩ := ih (i + 1)
        simp only [h_rec, bind_tc_ok]
        exact ⟨idx', opt', a :: newList', rfl⟩
      · exact ⟨i, some a, x :: rest, rfl⟩
      · exact ⟨i, none, x :: a :: rest, rfl⟩
    · simp [h_eq] at h_cmp
    · simp [h_eq] at h_cmp

/-- **Byte shift identity**: shifting a `U8` value left by 8 bits modulo `U16.size` equals
multiplication by 256.

• Since `b.val ≤ 255`, we have `b.val * 256 ≤ 65280 < 65536 = U16.size`, so the modular
  reduction is the identity. -/
private theorem u8_shl8_mod_u16_size (b : U8) :
    b.val <<< 8 % U16.size = b.val * 256 := by
  have hb : b.val ≤ 255 := by scalar_tac
  rw [Nat.shiftLeft_eq]
  simp only [Nat.reducePow]
  apply Nat.mod_eq_of_lt
  have : U16.size = 65536 := by scalar_tac
  omega

/-! ## Lagrange polynomial identity properties -/

/-- **Chunk point routing**: when `i < 16`, the total index `chunk_index * 16 + i` decomposes as

• `(chunk_index * 16 + i) % 16 = i` — the polynomial routing index.
• `(chunk_index * 16 + i) / 16 = chunk_index` — the evaluation point index.

This routing is the key structural property connecting `add_chunk` to the Lagrange interpolation
framework: iteration `i` contributes an evaluation point at x-coordinate `chunk_index` to
polynomial `i`.  When all chunks `0, 1, …, n−1` have been processed, polynomial `i` holds points
with x-coordinates `0, 1, …, n−1`, which is exactly the `completePoints` format required by
`from_complete_points`. -/
private lemma chunk_point_routing (chunk_index i : Nat) (h : i < 16) :
    (chunk_index * 16 + i) % 16 = i ∧
    (chunk_index * 16 + i) / 16 = chunk_index := by
  constructor <;> omega

set_option maxHeartbeats 8000000 in
-- haevy grind
/-- **Spec theorem for `body` (base case)**:

• Takes a `chunk`, an iterator range `iter`, and a `PolyDecoder` state `self`.
• On `ControlFlow.done`: returns the unchanged state and asserts the iterator is exhausted.
• On `ControlFlow.cont`: advances the iterator by one, preserves `pts_needed` and `is_complete`,
  and constructs a point `p` from the chunk data at the current iteration index.
• The point's x-coordinate is derived from the chunk index via integer division, and the
  y-coordinate is the big-endian encoding of two consecutive chunk data bytes.
• The point is either discarded (state unchanged) or inserted into the sorted point set at
  polynomial index `(chunk_index * 16 + i) % 16`.

The proof unfolds `body` and `sorted_vec.SortedSet.push`, then proceeds by case analysis on the
iterator range and the various insertion branches (`getLast?`, ordering comparison, and
`sortedInsert`).

**Source**: spqr/src/encoding/polynomial.rs (lines 882:12–903:13)
-/
@[step]
theorem body_spec_base
    (chunk : encoding.Chunk)
    (iter : core.ops.range.Range Usize)
    (self : encoding.polynomial.PolyDecoder)
    (h_end_le_16 : iter.end.val ≤ 16)
    (h_overflow : chunk.index.val * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 →
        (self.pts.val[k]!).val.length + 1 ≤ Usize.max) :
    body chunk iter self ⦃ cf =>
      match cf with
      | ControlFlow.done self' =>
          self' = self ∧ ¬(iter.start < iter.end)
      | ControlFlow.cont (iter1, self1) =>
          iter.start < iter.end ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          self1.pts_needed = self.pts_needed ∧
          self1.is_complete = self.is_complete ∧
          let i := iter.start.val
          let total_idx := chunk.index.val * 16 + i
          let poly := total_idx % 16
          let poly_idx := total_idx / 16
          ∃ (p : Pt),
            p.x.value.val = poly_idx ∧
            p.y.value.val = (chunk.data.val[i * 2]!).val * 256 + (chunk.data.val[i * 2 + 1]!).val ∧
            (self1 = self ∨
             ((∀ (k : Nat), k ≠ poly →
                 self1.pts.val[k]! = self.pts.val[k]!) ∧
              match (self.pts.val[poly]!).val.getLast? with
              | none =>
                  (self1.pts.val[poly]!).val =
                    (self.pts.val[poly]!).val ++ [p]
              | some last =>
                match Pt.Insts.CoreCmpOrd.cmp p last with
                | ok Ordering.gt =>
                    (self1.pts.val[poly]!).val =
                      (self.pts.val[poly]!).val ++ [p]
                | ok Ordering.eq =>
                    (self1.pts.val[poly]!).val =
                      (self.pts.val[poly]!).val.dropLast ++ [p]
                | ok Ordering.lt =>
                    ∃ (j : Nat),
                      j ≤ (self.pts.val[poly]!).val.length ∧
                      ((self1.pts.val[poly]!).val =
                          (self.pts.val[poly]!).val.take j ++ [p] ++
                          (self.pts.val[poly]!).val.drop j ∨
                       (j < (self.pts.val[poly]!).val.length ∧
                        (self1.pts.val[poly]!).val =
                          (self.pts.val[poly]!).val.take j ++ [p] ++
                          (self.pts.val[poly]!).val.drop (j + 1)))
                | _ => False)) ⦄ := by
  unfold body sorted_vec.SortedSet.push
  obtain ⟨⟨opt, iter1'⟩, hnext, h_none, h_some⟩ :=
    WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_spec' iter)
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_i_lt_16 : iter.start.val < 16 := by omega
    have h_2i_lt_32 : iter.start.val * 2 < 32 := by omega
    have h_2i1_lt_32 : iter.start.val * 2 + 1 < 32 := by omega
    have h_poly_lt_16 : (chunk.index.val * 16 + iter.start.val) % 16 < 16 := Nat.mod_lt _ (by omega)
    have h_shl : ∀ (b : U8), b.val <<< 8 % U16.size = b.val * 256 := u8_shl8_mod_u16_size
    step*
    · split
      · -- Branch 1: poly_idx < necessary_points, push with hroom true
        split
        · -- getLast? = none (empty set)
          step*
          constructor
          · exact h_lt
          · constructor
            · exact h_start1
            · constructor
              · exact h_end1
              · refine ⟨Pt.mk x y, ?_, ?_, ?_⟩
                · simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos,
                  Order.add_one_le_iff, not_true_eq_false, reduceCtorEq, false_and, implies_true,
                  and_self,  UScalarTy.U16_numBits_eq,
                  UScalarTy.Usize_numBits_eq, System.Platform.sixteen_le_numBits,
                  UScalar.cast_val_mod_pow_greater_numBits_eq, UScalarTy.U8_numBits_eq,
                  Nat.reduceLeDiff, Bvify.U16.UScalar_bv, Bvify.UScalar.cast_bv,
                  Bvify.U8.UScalar_bv,
                  UScalar.lt_equiv, Nat.mul_add_mod_self_right, List.getLast?_eq_none_iff,
                  UScalar.cast_val_eq, Nat.reducePow, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one,
                  Nat.reduceAdd, List.length_nil]
                  scalar_tac
                · simp_all
                · right
                  constructor
                  · intro k hk
                    simp_all
                  · split
                    · have hlen : (↑iter.start % 16) < self.pts.val.length := by scalar_tac
                      simp_all
                    · split
                      · simp_all
                        grind
                      · grind
                      · grind
                      · grind
        · -- getLast? = some last
          step*
          split
          · -- Ordering.gt
            step*
            constructor
            · exact h_lt
            · constructor
              · exact h_start1
              · constructor
                · exact h_end1
                · refine ⟨Pt.mk x y, ?_, ?_, ?_⟩
                  · simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos,
                    Order.add_one_le_iff, not_true_eq_false, reduceCtorEq, false_and, implies_true,
                    and_self,  UScalarTy.U16_numBits_eq,
                    UScalarTy.Usize_numBits_eq, System.Platform.sixteen_le_numBits,
                    UScalar.cast_val_mod_pow_greater_numBits_eq, UScalarTy.U8_numBits_eq,
                    Nat.reduceLeDiff, Bvify.U16.UScalar_bv, Bvify.UScalar.cast_bv,
                    Bvify.U8.UScalar_bv, UScalar.lt_equiv, Nat.mul_add_mod_self_right,
                    UScalar.cast_val_eq, Nat.reducePow, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one,
                    Nat.reduceAdd]
                    scalar_tac
                  · simp_all
                  · right
                    constructor
                    · intro k hk
                      simp_all
                    · split
                      · have hlen : (↑iter.start % 16) < self.pts.val.length := by scalar_tac
                        simp_all
                      · split
                        · simp_all
                          grind
                        · grind [Pt.Insts.CoreCmpOrd.cmp_spec]
                        · grind [Pt.Insts.CoreCmpOrd.cmp_spec]
                        · have h_absurd : ∀ (a b : Pt),
                              (Pt.Insts.CoreCmpOrd.cmp a b = ok Ordering.gt → False) →
                              (Pt.Insts.CoreCmpOrd.cmp a b = ok Ordering.eq → False) →
                              (Pt.Insts.CoreCmpOrd.cmp a b = ok Ordering.lt → False) →
                              False := by
                            intro a b hgt heq hlt
                            obtain ⟨r, hr, -⟩ :=
                              WP.spec_imp_exists (Pt.Insts.CoreCmpOrd.cmp_spec a b)
                            cases r
                            · exact hlt hr
                            · exact heq hr
                            · exact hgt hr
                          exact h_absurd _ _
                            (by assumption) (by assumption) (by assumption)
          · -- Ordering.eq
            step*
            · constructor
              · exact h_lt
              · constructor
                · exact h_start1
                · constructor
                  · exact h_end1
                  · refine ⟨Pt.mk x y, ?_, ?_, ?_⟩
                    · simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos,
                      Order.add_one_le_iff, not_true_eq_false, reduceCtorEq,
                      false_and, implies_true, and_self,  UScalarTy.U16_numBits_eq,
                      UScalarTy.Usize_numBits_eq, System.Platform.sixteen_le_numBits,
                      UScalar.cast_val_mod_pow_greater_numBits_eq, UScalarTy.U8_numBits_eq,
                      Nat.reduceLeDiff, Bvify.U16.UScalar_bv, Bvify.UScalar.cast_bv,
                      Bvify.U8.UScalar_bv, UScalar.lt_equiv, Nat.mul_add_mod_self_right,
                      UScalar.cast_val_eq, Nat.reducePow, Nat.mod_succ_eq_iff_lt,
                      Nat.succ_eq_add_one,
                      Nat.reduceAdd]
                      scalar_tac
                    · simp_all
                    · right
                      constructor
                      · intro k hk
                        simp_all
                      · split
                        · have hlen : (↑iter.start % 16) < self.pts.val.length := by scalar_tac
                          simp_all
                        · split
                          · exfalso
                            grind [Pt.Insts.CoreCmpOrd.cmp_spec]
                          · simp_all
                            grind
                          · exfalso
                            grind [Pt.Insts.CoreCmpOrd.cmp_spec]
                          · have h_absurd : ∀ (a b : Pt),
                                (Pt.Insts.CoreCmpOrd.cmp a b = ok Ordering.gt → False) →
                                (Pt.Insts.CoreCmpOrd.cmp a b = ok Ordering.eq → False) →
                                (Pt.Insts.CoreCmpOrd.cmp a b = ok Ordering.lt → False) →
                                False := by
                              intro a b hgt heq hlt
                              obtain ⟨r, hr, -⟩ :=
                                WP.spec_imp_exists (Pt.Insts.CoreCmpOrd.cmp_spec a b)
                              cases r
                              · exact hlt hr
                              · exact heq hr
                              · exact hgt hr
                            exact h_absurd _ _
                              (by assumption) (by assumption) (by assumption)
          · -- Ordering.lt (sortedInsert)
            obtain ⟨idx_si, opt_si, newList_si, h_si⟩ :=
              sortedInsert_always_ok ss.val (Pt.mk x y) 0
            simp only [h_si]
            have hbnd : newList_si.length ≤ Usize.max ∧ idx_si ≤ Usize.max := by
              have h_spec := sorted_vec.SortedSet.sortedInsert_spec Pt.Insts.CoreCmpOrd
                  ss.val (Pt.mk x y) 0 h_si
              obtain ⟨k_si, hk_idx, hk_le, hk_prop⟩ := h_spec
              constructor
              · rcases hk_prop with h_ins | ⟨_, h_rep⟩
                · rw [h_ins]; simp [List.length_append, List.length_take, List.length_drop]
                  grind
                · rw [h_rep]; simp [List.length_append, List.length_take, List.length_drop]
                  grind
              · grind
            simp only [dif_pos hbnd]
            step*
            constructor
            · exact h_lt
            · constructor
              · exact h_start1
              · constructor
                · exact h_end1
                · refine ⟨Pt.mk x y, ?_, ?_, ?_⟩
                  · simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos,
                    Order.add_one_le_iff, not_true_eq_false, reduceCtorEq, false_and, implies_true,
                    and_self,  UScalarTy.U16_numBits_eq,
                    UScalarTy.Usize_numBits_eq, System.Platform.sixteen_le_numBits,
                    UScalar.cast_val_mod_pow_greater_numBits_eq, UScalarTy.U8_numBits_eq,
                    Nat.reduceLeDiff, Bvify.U16.UScalar_bv, Bvify.UScalar.cast_bv,
                    Bvify.U8.UScalar_bv, UScalar.lt_equiv, Nat.mul_add_mod_self_right,
                    UScalar.cast_val_eq, Nat.reducePow, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one,
                    Nat.reduceAdd]
                    scalar_tac
                  · simp_all
                  · right
                    constructor
                    · intro k hk; simp_all
                    · split
                      · have hlen : (↑iter.start % 16) < self.pts.val.length := by scalar_tac
                        simp_all
                      · split
                        · grind [Pt.Insts.CoreCmpOrd.cmp_spec]
                        · grind [Pt.Insts.CoreCmpOrd.cmp_spec]
                        · have h_spec := sorted_vec.SortedSet.sortedInsert_spec Pt.Insts.CoreCmpOrd
                              ss.val (Pt.mk x y) 0 h_si
                          obtain ⟨k, _, hk_le, hk_prop⟩ := h_spec
                          simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq,
                            getElem!_pos, Order.add_one_le_iff, not_true_eq_false, reduceCtorEq,
                            false_and, implies_true,  and_self,
                            UScalarTy.U16_numBits_eq, UScalarTy.Usize_numBits_eq,
                            System.Platform.sixteen_le_numBits,
                            UScalar.cast_val_mod_pow_greater_numBits_eq, UScalarTy.U8_numBits_eq,
                            Nat.reduceLeDiff, Bvify.U16.UScalar_bv, Bvify.UScalar.cast_bv,
                            Bvify.U8.UScalar_bv, UScalar.lt_equiv, Nat.mul_add_mod_self_right,
                            UScalar.cast_val_eq, Nat.reducePow, zero_add,
                            List.getElem!_eq_getElem?_getD, List.append_assoc, List.cons_append,
                            List.nil_append, Array.set_val_eq]
                          exact ⟨k, by grind, by grind⟩
                        · have h_absurd : ∀ (a b : Pt),
                              (Pt.Insts.CoreCmpOrd.cmp a b = ok Ordering.gt → False) →
                              (Pt.Insts.CoreCmpOrd.cmp a b = ok Ordering.eq → False) →
                              (Pt.Insts.CoreCmpOrd.cmp a b = ok Ordering.lt → False) →
                              False := by
                            intro a b hgt heq hlt
                            obtain ⟨r, hr, -⟩ :=
                              WP.spec_imp_exists (Pt.Insts.CoreCmpOrd.cmp_spec a b)
                            cases r
                            · exact hlt hr
                            · exact heq hr
                            · exact hgt hr
                          exact h_absurd _ _
                            (by assumption) (by assumption) (by assumption)
      · -- Branch 2: overflow impossible (hroom false)
        step*
        have := h_push_cap (↑iter.start % 16) (by omega)
        grind
    · -- Branch 3: second push path (¬ poly_idx < np, len < np)
      have h_len := h_push_cap (↑iter.start % 16) (by omega)
      split
      · split
        · step*
          constructor
          · exact h_lt
          · constructor
            · exact h_start1
            · constructor
              · exact h_end1
              · refine ⟨Pt.mk x y, ?_, ?_, ?_⟩
                · simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos,
                  Order.add_one_le_iff, not_true_eq_false, reduceCtorEq, false_and, implies_true,
                  and_self,  UScalarTy.U16_numBits_eq,
                  UScalarTy.Usize_numBits_eq, System.Platform.sixteen_le_numBits,
                  UScalar.cast_val_mod_pow_greater_numBits_eq, UScalarTy.U8_numBits_eq,
                  Nat.reduceLeDiff, Bvify.U16.UScalar_bv, Bvify.UScalar.cast_bv,
                  Bvify.U8.UScalar_bv, UScalar.lt_equiv, not_lt, Nat.mul_add_mod_self_right,
                  alloc.vec.Vec.len, Usize.ofNatCore_val_eq, List.getElem!_eq_getElem?_getD,
                  List.getLast?_eq_none_iff, UScalar.cast_val_eq, Nat.reducePow,
                  Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd, List.length_nil,
                  add_pos_iff, Nat.div_pos_iff, Nat.ofNat_pos, true_and]
                  scalar_tac
                · simp_all
                · right
                  constructor
                  · intro k hk; simp_all
                  · split
                    · have hlen : (↑iter.start % 16) < self.pts.val.length := by scalar_tac
                      simp_all
                    · split
                      · grind [Pt.Insts.CoreCmpOrd.cmp_spec]
                      · grind [Pt.Insts.CoreCmpOrd.cmp_spec]
                      · grind
                      · have h_absurd : ∀ (a b : Pt),
                            (Pt.Insts.CoreCmpOrd.cmp a b = ok Ordering.gt → False) →
                            (Pt.Insts.CoreCmpOrd.cmp a b = ok Ordering.eq → False) →
                            (Pt.Insts.CoreCmpOrd.cmp a b = ok Ordering.lt → False) →
                            False := by
                          intro a b hgt heq hlt
                          obtain ⟨r, hr, -⟩ :=
                            WP.spec_imp_exists (Pt.Insts.CoreCmpOrd.cmp_spec a b)
                          cases r
                          · exact hlt hr
                          · exact heq hr
                          · exact hgt hr
                        exact h_absurd _ _
                          (by assumption) (by assumption) (by assumption)
        · step*
          split
          · step*
            constructor
            · exact h_lt
            · constructor
              · exact h_start1
              · constructor
                · exact h_end1
                · refine ⟨Pt.mk x y, ?_, ?_, ?_⟩
                  · simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos,
                    Order.add_one_le_iff, not_true_eq_false, reduceCtorEq, false_and, implies_true,
                     and_self,  UScalarTy.U16_numBits_eq,
                    UScalarTy.Usize_numBits_eq, System.Platform.sixteen_le_numBits,
                    UScalar.cast_val_mod_pow_greater_numBits_eq, UScalarTy.U8_numBits_eq,
                    Nat.reduceLeDiff, Bvify.U16.UScalar_bv, Bvify.UScalar.cast_bv,
                    Bvify.U8.UScalar_bv, UScalar.lt_equiv, not_lt, Nat.mul_add_mod_self_right,
                    alloc.vec.Vec.len, Usize.ofNatCore_val_eq, List.getElem!_eq_getElem?_getD,
                    UScalar.cast_val_eq, Nat.reducePow, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one,
                    Nat.reduceAdd]
                    scalar_tac
                  · simp_all
                  · right
                    constructor
                    · intro k hk; simp_all
                    · split
                      · have hlen : (↑iter.start % 16) < self.pts.val.length := by scalar_tac
                        simp_all
                      · split
                        · simp_all
                          grind
                        · grind [Pt.Insts.CoreCmpOrd.cmp_spec]
                        · grind [Pt.Insts.CoreCmpOrd.cmp_spec]
                        · have h_absurd : ∀ (a b : Pt),
                            (Pt.Insts.CoreCmpOrd.cmp a b = ok Ordering.gt → False) →
                            (Pt.Insts.CoreCmpOrd.cmp a b = ok Ordering.eq → False) →
                            (Pt.Insts.CoreCmpOrd.cmp a b = ok Ordering.lt → False) →
                            False := by
                              intro a b hgt heq hlt
                              obtain ⟨r, hr, -⟩ :=
                                WP.spec_imp_exists (Pt.Insts.CoreCmpOrd.cmp_spec a b)
                              cases r
                              · exact hlt hr
                              · exact heq hr
                              · exact hgt hr
                          exact h_absurd _ _
                                (by assumption) (by assumption) (by assumption)
          · step*
            constructor
            · exact h_lt
            · constructor
              · exact h_start1
              · constructor
                · exact h_end1
                · refine ⟨Pt.mk x y, ?_, ?_, ?_⟩
                  · simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos,
                    Order.add_one_le_iff, not_true_eq_false, reduceCtorEq, false_and, implies_true,
                    and_self,  UScalarTy.U16_numBits_eq,
                    UScalarTy.Usize_numBits_eq, System.Platform.sixteen_le_numBits,
                    UScalar.cast_val_mod_pow_greater_numBits_eq, UScalarTy.U8_numBits_eq,
                    Nat.reduceLeDiff, Bvify.U16.UScalar_bv, Bvify.UScalar.cast_bv,
                    Bvify.U8.UScalar_bv, UScalar.lt_equiv, not_lt, Nat.mul_add_mod_self_right,
                    alloc.vec.Vec.len, Usize.ofNatCore_val_eq, List.getElem!_eq_getElem?_getD,
                    UScalar.cast_val_eq, Nat.reducePow, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one,
                    Nat.reduceAdd]
                    scalar_tac
                  · simp_all
                  · right
                    constructor
                    · intro k hk; simp_all
                    · split
                      · have hlen : (↑iter.start % 16) < self.pts.val.length := by scalar_tac
                        simp_all
                      · split
                        · grind [Pt.Insts.CoreCmpOrd.cmp_spec]
                        · simp_all
                          grind
                        · grind [Pt.Insts.CoreCmpOrd.cmp_spec]
                        · have h_absurd : ∀ (a b : Pt),
                              (Pt.Insts.CoreCmpOrd.cmp a b = ok Ordering.gt → False) →
                              (Pt.Insts.CoreCmpOrd.cmp a b = ok Ordering.eq → False) →
                              (Pt.Insts.CoreCmpOrd.cmp a b = ok Ordering.lt → False) →
                              False := by
                            intro a b hgt heq hlt
                            obtain ⟨r, hr, -⟩ :=
                              WP.spec_imp_exists (Pt.Insts.CoreCmpOrd.cmp_spec a b)
                            cases r
                            · exact hlt hr
                            · exact heq hr
                            · exact hgt hr
                          exact h_absurd _ _
                            (by assumption) (by assumption) (by assumption)
          · obtain ⟨idx_si, opt_si, newList_si, h_si⟩ :=
              sortedInsert_always_ok ss.val (Pt.mk x y) 0
            simp only [h_si]
            have hbnd : newList_si.length ≤ Usize.max ∧ idx_si ≤ Usize.max := by
              have h_spec := sorted_vec.SortedSet.sortedInsert_spec Pt.Insts.CoreCmpOrd
                  ss.val (Pt.mk x y) 0 h_si
              obtain ⟨k_si, hk_idx, hk_le, hk_prop⟩ := h_spec
              constructor
              · rcases hk_prop with h_ins | ⟨_, h_rep⟩
                · rw [h_ins]; simp [List.length_append, List.length_take, List.length_drop]
                  grind
                · rw [h_rep]; simp [List.length_append, List.length_take, List.length_drop]
                  grind
              · grind
            simp only [dif_pos hbnd]
            step*
            constructor
            · exact h_lt
            · constructor
              · exact h_start1
              · constructor
                · exact h_end1
                · refine ⟨Pt.mk x y, ?_, ?_, ?_⟩
                  · simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos,
                    Order.add_one_le_iff, not_true_eq_false, reduceCtorEq, false_and, implies_true,
                    and_self,  UScalarTy.U16_numBits_eq,
                    UScalarTy.Usize_numBits_eq, System.Platform.sixteen_le_numBits,
                    UScalar.cast_val_mod_pow_greater_numBits_eq, UScalarTy.U8_numBits_eq,
                    Nat.reduceLeDiff, Bvify.U16.UScalar_bv, Bvify.UScalar.cast_bv,
                    Bvify.U8.UScalar_bv, UScalar.lt_equiv, not_lt, Nat.mul_add_mod_self_right,
                    alloc.vec.Vec.len, Usize.ofNatCore_val_eq, List.getElem!_eq_getElem?_getD,
                    UScalar.cast_val_eq, Nat.reducePow, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one,
                    Nat.reduceAdd]
                    scalar_tac
                  · simp_all
                  · right
                    constructor
                    · intro k hk; simp_all
                    · split
                      · have hlen : (↑iter.start % 16) < self.pts.val.length := by scalar_tac
                        simp_all
                      · split
                        · grind [Pt.Insts.CoreCmpOrd.cmp_spec]
                        · grind [Pt.Insts.CoreCmpOrd.cmp_spec]
                        · have h_spec := sorted_vec.SortedSet.sortedInsert_spec Pt.Insts.CoreCmpOrd
                              ss.val (Pt.mk x y) 0 h_si
                          obtain ⟨k, _, hk_le, hk_prop⟩ := h_spec
                          simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq,
                          getElem!_pos,
                            Order.add_one_le_iff, not_true_eq_false, reduceCtorEq, false_and,
                            implies_true,  and_self,
                            UScalarTy.U16_numBits_eq, UScalarTy.Usize_numBits_eq,
                            System.Platform.sixteen_le_numBits,
                            UScalar.cast_val_mod_pow_greater_numBits_eq, UScalarTy.U8_numBits_eq,
                            Nat.reduceLeDiff, Bvify.U16.UScalar_bv, Bvify.UScalar.cast_bv,
                            Bvify.U8.UScalar_bv, UScalar.lt_equiv, not_lt,
                            Nat.mul_add_mod_self_right,
                            alloc.vec.Vec.len, Usize.ofNatCore_val_eq,
                            List.getElem!_eq_getElem?_getD,
                            UScalar.cast_val_eq, Nat.reducePow, zero_add, List.append_assoc,
                            List.cons_append, List.nil_append, Array.set_val_eq]
                          exact ⟨k, by grind, by grind⟩
                        · have h_absurd : ∀ (a b : Pt),
                              (Pt.Insts.CoreCmpOrd.cmp a b = ok Ordering.gt → False) →
                              (Pt.Insts.CoreCmpOrd.cmp a b = ok Ordering.eq → False) →
                              (Pt.Insts.CoreCmpOrd.cmp a b = ok Ordering.lt → False) →
                              False := by
                            intro a b hgt heq hlt
                            obtain ⟨r, hr, -⟩ :=
                              WP.spec_imp_exists (Pt.Insts.CoreCmpOrd.cmp_spec a b)
                            cases r
                            · exact hlt hr
                            · exact heq hr
                            · exact hgt hr
                          exact h_absurd _ _
                            (by assumption) (by assumption) (by assumption)
      · grind
    · -- Branch 4: skip (self unchanged)
      constructor
      · exact h_lt
      · constructor
        · exact h_start1
        · constructor
          · exact h_end1
          · use (Pt.mk x y)
            constructor
            · simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos,
              Order.add_one_le_iff, not_true_eq_false, reduceCtorEq, false_and, implies_true,
              and_self,  UScalarTy.U16_numBits_eq,
              UScalarTy.Usize_numBits_eq, System.Platform.sixteen_le_numBits,
              UScalar.cast_val_mod_pow_greater_numBits_eq, UScalarTy.U8_numBits_eq,
              Nat.reduceLeDiff, Bvify.U16.UScalar_bv, Bvify.UScalar.cast_bv, Bvify.U8.UScalar_bv,
              UScalar.lt_equiv, not_lt, Nat.mul_add_mod_self_right, alloc.vec.Vec.len,
              Usize.ofNatCore_val_eq, UScalar.cast_val_eq, Nat.reducePow, Nat.mod_succ_eq_iff_lt,
              Nat.succ_eq_add_one, Nat.reduceAdd]
              scalar_tac
            · simp_all
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

/-- **Spec theorem for `body` (Lagrange-enriched)**:

• Takes a `chunk`, an iterator range `iter`, and a `PolyDecoder` state `self`.
• Strengthens `body_spec_0` with explicit Lagrange polynomial identity properties.
• On `ControlFlow.done`: returns the unchanged state when the iterator is exhausted.
• On `ControlFlow.cont`: advances the iterator and inserts a point into the appropriate
  polynomial's sorted set.

In addition to all of `body_spec_0`'s postconditions, this theorem establishes:

• `poly < 16` — the polynomial routing index is bounded, ensuring the point is directed to a
  valid polynomial in the 16-polynomial array.
• `poly_idx = chunk.index.val` — the evaluation point index equals the chunk index, the key
  structural property connecting `add_chunk` to the Lagrange interpolation framework.

When all chunks `0, 1, …, n−1` have been processed, polynomial `i` holds points with
x-coordinates `0, 1, …, n−1`, which is exactly the `completePoints` format required by
`from_complete_points` for computing the Lagrange interpolation sum
  `p.toGF216Poly = Σⱼ C(pts[j].y.toGF216) * scaledLagrangeBasis(len, j)`.

The four downstream Lagrange identities (`poly_identity_from`,
`coeff_zero_eq_zero_of_X_mul_identity`, `mult_xdiff_result_eq`,
`natDegree_lagrangeBasisPoly_le`) are not included in this postcondition because they concern
the interpolation computation that happens after all points have been collected, not the point
insertion step verified here.  They are proved in `Poly/LagrangeInterpolate.lean`,
`Poly/LagrangeInterpolatePrepare.lean`, and `Poly/LagrangeInterpolateComplete.lean`.

The proof applies `WP.spec_mono` to `body_spec_0` and discharges the additional Lagrange
properties using `chunk_point_routing`.

**Source**: spqr/src/encoding/polynomial.rs (lines 882:12–903:13)
-/
@[step]
theorem body_spec
    (chunk : encoding.Chunk)
    (iter : core.ops.range.Range Usize)
    (self : encoding.polynomial.PolyDecoder)
    (h_end_le_16 : iter.end.val ≤ 16)
    (h_overflow : chunk.index.val * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 →
        (self.pts.val[k]!).val.length + 1 ≤ Usize.max) :
    body chunk iter self ⦃ cf =>
      match cf with
      | ControlFlow.done self' =>
          self' = self ∧ ¬(iter.start < iter.end)
      | ControlFlow.cont (iter1, self1) =>
          iter.start < iter.end ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          self1.pts_needed = self.pts_needed ∧
          self1.is_complete = self.is_complete ∧
          let i := iter.start.val
          let total_idx := chunk.index.val * 16 + i
          let poly := total_idx % 16
          let poly_idx := total_idx / 16
          -- Lagrange polynomial identity properties:
          poly < 16 ∧
          poly_idx = chunk.index.val ∧
          ∃ (p : Pt),
            p.x.value.val = poly_idx ∧
            p.y.value.val = (chunk.data.val[i * 2]!).val * 256 + (chunk.data.val[i * 2 + 1]!).val ∧
            (self1 = self ∨
             ((∀ (k : Nat), k ≠ poly →
                 self1.pts.val[k]! = self.pts.val[k]!) ∧
              match (self.pts.val[poly]!).val.getLast? with
              | none =>
                  (self1.pts.val[poly]!).val =
                    (self.pts.val[poly]!).val ++ [p]
              | some last =>
                match Pt.Insts.CoreCmpOrd.cmp p last with
                | ok Ordering.gt =>
                    (self1.pts.val[poly]!).val =
                      (self.pts.val[poly]!).val ++ [p]
                | ok Ordering.eq =>
                    (self1.pts.val[poly]!).val =
                      (self.pts.val[poly]!).val.dropLast ++ [p]
                | ok Ordering.lt =>
                    ∃ (j : Nat),
                      j ≤ (self.pts.val[poly]!).val.length ∧
                      ((self1.pts.val[poly]!).val =
                          (self.pts.val[poly]!).val.take j ++ [p] ++
                          (self.pts.val[poly]!).val.drop j ∨
                       (j < (self.pts.val[poly]!).val.length ∧
                        (self1.pts.val[poly]!).val =
                          (self.pts.val[poly]!).val.take j ++ [p] ++
                          (self.pts.val[poly]!).val.drop (j + 1)))
                | _ => False)) ⦄ := by
  apply WP.spec_mono (body_spec_base chunk iter self h_end_le_16 h_overflow h_push_cap)
  intro cf hcf
  match cf with
  | ControlFlow.done _ => exact hcf
  | ControlFlow.cont (_, _) =>
    obtain ⟨h1, h2, h3, h4, h5, p, hp_x, hp_y, h_upd⟩ := hcf
    have h_i_lt_16 : iter.start.val < 16 := by scalar_tac
    have h_routing := chunk_point_routing chunk.index.val iter.start.val h_i_lt_16
    exact ⟨h1, h2, h3, h4, h5, Nat.mod_lt _ (by omega), h_routing.2, p, hp_x, hp_y, h_upd⟩

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop

/-! # Spec theorem for `PolyDecoder::add_chunk`: loop 0

Drives the `add_chunk` body to completion over the range `[iter.start, iter.end)`.  The loop
iterates a `Range<usize>` with step 1; the proof uses `loop.spec_decr_nat` with measure
`iter.end − iter.start`.

Each iteration `j` (with `i = iter.start + j`) computes `total_idx = chunk.index * 16 + i`,
`poly = total_idx % 16`, `poly_idx = total_idx / 16`, builds a point
`Pt { x = GF16::new(poly_idx), y = GF16::new((data[2i] << 8) + data[2i+1]) }`,
and conditionally pushes it onto `self.pts[poly]` via `SortedSet::push`.

The loop invariant tracks: the iterator end is unchanged, `pts_needed` and `is_complete` are
preserved, the push capacity is maintained (with room proportional to the remaining iteration
count), and there is a chain of intermediate decoder states `selfs 0 = self, …, selfs n =
current` with per-step point-insertion witnesses matching the body specification.

**Source**: spqr/src/encoding/polynomial.rs (lines 882:8-903:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop

private theorem body_pts_length_le
    (self1 self' : encoding.polynomial.PolyDecoder) (p : Pt) (poly : Nat)
    (h_update :
      self1 = self' ∨
      ((∀ (k : Nat), k ≠ poly →
          self1.pts.val[k]! = self'.pts.val[k]!) ∧
       match (self'.pts.val[poly]!).val.getLast? with
       | none =>
           (self1.pts.val[poly]!).val =
             (self'.pts.val[poly]!).val ++ [p]
       | some last =>
         match Pt.Insts.CoreCmpOrd.cmp p last with
         | ok Ordering.gt =>
             (self1.pts.val[poly]!).val =
               (self'.pts.val[poly]!).val ++ [p]
         | ok Ordering.eq =>
             (self1.pts.val[poly]!).val =
               (self'.pts.val[poly]!).val.dropLast ++ [p]
         | ok Ordering.lt =>
             ∃ (m : Nat),
               m ≤ (self'.pts.val[poly]!).val.length ∧
               ((self1.pts.val[poly]!).val =
                   (self'.pts.val[poly]!).val.take m ++ [p] ++
                   (self'.pts.val[poly]!).val.drop m ∨
                (m < (self'.pts.val[poly]!).val.length ∧
                 (self1.pts.val[poly]!).val =
                   (self'.pts.val[poly]!).val.take m ++ [p] ++
                   (self'.pts.val[poly]!).val.drop (m + 1)))
         | _ => False))
    (k : Nat) :
    (self1.pts.val[k]!).val.length ≤
      (self'.pts.val[k]!).val.length + 1 := by
  rcases h_update with h_eq | ⟨h_frame, h_push⟩
  · subst h_eq
    omega
  · by_cases hk : k = poly
    · subst hk
      split at h_push
      · -- none (empty): append
        simp
        grind
      · -- some last
        split at h_push
        · simp
          grind
        · simp
          grind
        · obtain ⟨m, _, h | ⟨hm, h⟩⟩ := h_push <;>
            simp  <;>
            grind
        · exact absurd h_push id
    · rw [h_frame k hk]; omega

/-- **Spec theorem for `PolyDecoder::add_chunk_loop`** (loop 0):

• Iterates the body over `[iter.start, iter.end)` with `iter.end ≤ 16`.
• Returns a decoder whose `pts_needed` and `is_complete` fields are unchanged.
• Witnesses the iteration via a chain of `n = iter.end − iter.start` intermediate states
  `selfs 0 = self, …, selfs n = result` where each step `j` constructs a point `p` with
  - `p.x.value.val = (chunk.index * 16 + iter.start + j) / 16`
  - `p.y.value.val = chunk.data[(iter.start + j) * 2] * 256 +
                      chunk.data[(iter.start + j) * 2 + 1]`
  and either leaves the decoder unchanged or pushes `p` onto `pts[poly]` (with
  `poly = (chunk.index * 16 + iter.start + j) % 16`) via `SortedSet::push`, with the
  same push semantics as `body_spec`.

The precondition `h_push_cap` reserves `iter.end − iter.start + 1` capacity slots per sorted
set; since each iteration can grow one sorted set by at most one element, the capacity bound
decreases in tandem with the remaining iteration count, maintaining the body's
`length + 1 ≤ Usize.max` requirement at every step.

**Source**: spqr/src/encoding/polynomial.rs (lines 882:8-903:9) -/
@[step]
theorem loop_spec
    (chunk : encoding.Chunk)
    (iter : core.ops.range.Range Usize)
    (self : encoding.polynomial.PolyDecoder)
    (h_end_le_16 : iter.end.val ≤ 16)
    (h_start_le : iter.start ≤ iter.end)
    (h_overflow : chunk.index.val * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 →
        (self.pts[k]!).length + (iter.end - iter.start) + 1 ≤ Usize.max) :
    add_chunk_loop iter self chunk ⦃ (result : PolyDecoder) =>
      result.pts_needed = self.pts_needed ∧
      result.is_complete = self.is_complete ∧
      ∃ (selfs : Nat → PolyDecoder),
        selfs 0 = self ∧
        selfs (iter.end - iter.start) = result ∧
        iter.end - iter.start = iter.end - iter.start ∧
        ∀ (j : Nat), j < iter.end - iter.start →
          let i := iter.start + j
          let total_idx := chunk.index.val * 16 + i
          let poly := total_idx % 16
          let poly_idx := total_idx / 16
          (selfs (j + 1)).pts_needed = self.pts_needed ∧
          (selfs (j + 1)).is_complete = self.is_complete ∧
          poly < 16 ∧
          poly_idx = chunk.index.val ∧
          ∃ (p : Pt),
            p.x.value.val = poly_idx ∧
            p.y.value.val = (chunk.data[i * 2]!) * 256 + (chunk.data[i * 2 + 1]!) ∧
            (selfs (j + 1) = selfs j ∨
             ((∀ (k : Nat), k ≠ poly →
                 (selfs (j + 1)).pts[k]! = (selfs j).pts.val[k]!) ∧
              match ((selfs j).pts.val[poly]!).val.getLast? with
              | none =>
                  ((selfs (j + 1)).pts.val[poly]!).val =
                    ((selfs j).pts.val[poly]!).val ++ [p]
              | some last =>
                match Pt.Insts.CoreCmpOrd.cmp p last with
                | ok Ordering.gt =>
                    ((selfs (j + 1)).pts.val[poly]!).val =
                      ((selfs j).pts.val[poly]!).val ++ [p]
                | ok Ordering.eq =>
                    ((selfs (j + 1)).pts.val[poly]!).val =
                      ((selfs j).pts.val[poly]!).val.dropLast ++ [p]
                | ok Ordering.lt =>
                    ∃ (m : Nat),
                      m ≤ ((selfs j).pts.val[poly]!).val.length ∧
                      (((selfs (j + 1)).pts.val[poly]!).val =
                          ((selfs j).pts.val[poly]!).val.take m ++ [p] ++
                          ((selfs j).pts.val[poly]!).val.drop m ∨
                       (m < ((selfs j).pts.val[poly]!).val.length ∧
                        ((selfs (j + 1)).pts.val[poly]!).val =
                          ((selfs j).pts.val[poly]!).val.take m ++ [p] ++
                          ((selfs j).pts.val[poly]!).val.drop (m + 1)))
                | _ => False)) ⦄ := by
  unfold add_chunk_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × PolyDecoder) => p.1.end - p.1.start)
    (inv := fun (p : core.ops.range.Range Usize × PolyDecoder) =>
      p.1.end = iter.end ∧
      iter.start ≤ p.1.start ∧
      p.1.start.val ≤ p.1.end.val ∧
      p.2.pts_needed = self.pts_needed ∧
      p.2.is_complete = self.is_complete ∧
      (∀ (k : Nat), k < 16 →
          (p.2.pts.val[k]!).val.length +
            (p.1.end.val - p.1.start.val) + 1 ≤ Usize.max) ∧
      ∃ (n : Nat) (selfs : Nat → PolyDecoder),
        selfs 0 = self ∧ selfs n = p.2 ∧
        n = p.1.start.val - iter.start.val ∧
        ∀ (j : Nat), j < n →
          let i := iter.start.val + j
          let total_idx := chunk.index.val * 16 + i
          let poly := total_idx % 16
          let poly_idx := total_idx / 16
          (selfs (j + 1)).pts_needed = self.pts_needed ∧
          (selfs (j + 1)).is_complete = self.is_complete ∧
          poly < 16 ∧
          poly_idx = chunk.index.val ∧
          ∃ (p : Pt),
            p.x.value.val = poly_idx ∧
            p.y.value.val =
              (chunk.data.val[i * 2]!).val * 256 +
              (chunk.data.val[i * 2 + 1]!).val ∧
            (selfs (j + 1) = selfs j ∨
             ((∀ (k : Nat), k ≠ poly →
                 (selfs (j + 1)).pts.val[k]! = (selfs j).pts.val[k]!) ∧
              match ((selfs j).pts.val[poly]!).val.getLast? with
              | none =>
                  ((selfs (j + 1)).pts.val[poly]!).val =
                    ((selfs j).pts.val[poly]!).val ++ [p]
              | some last =>
                match Pt.Insts.CoreCmpOrd.cmp p last with
                | ok Ordering.gt =>
                    ((selfs (j + 1)).pts.val[poly]!).val =
                      ((selfs j).pts.val[poly]!).val ++ [p]
                | ok Ordering.eq =>
                    ((selfs (j + 1)).pts.val[poly]!).val =
                      ((selfs j).pts.val[poly]!).val.dropLast ++ [p]
                | ok Ordering.lt =>
                    ∃ (m : Nat),
                      m ≤ ((selfs j).pts.val[poly]!).val.length ∧
                      (((selfs (j + 1)).pts.val[poly]!).val =
                          ((selfs j).pts.val[poly]!).val.take m ++ [p] ++
                          ((selfs j).pts.val[poly]!).val.drop m ∨
                       (m < ((selfs j).pts.val[poly]!).val.length ∧
                        ((selfs (j + 1)).pts.val[poly]!).val =
                          ((selfs j).pts.val[poly]!).val.take m ++ [p] ++
                          ((selfs j).pts.val[poly]!).val.drop (m + 1)))
                | _ => False)))
  · rintro ⟨iter', self'⟩ ⟨h_end', h_orig_le, h_le', h_pn', h_ic', h_cap',
            n, selfs', h_s0, h_sn, h_n, h_chain⟩
    simp only [] at h_end' h_orig_le h_le' h_pn' h_ic' h_cap' h_s0 h_sn h_n h_chain ⊢
    have h_end_val : iter'.end.val = iter.end.val := by rw [h_end']
    have h_push_cap' : ∀ k, k < 16 →
        (self'.pts.val[k]!).val.length + 1 ≤ Usize.max := by
      intro k hk; have := h_cap' k hk; omega
    have h_body := body_spec chunk iter' self'
      (by rw [h_end_val]; exact h_end_le_16) h_overflow h_push_cap'
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done self_final =>
      simp only [] at h_cf ⊢
      obtain ⟨h_eq, h_not_lt⟩ := h_cf
      subst h_eq
      refine ⟨h_pn', h_ic', selfs', h_s0, by grind, by grind, by grind⟩
    | ControlFlow.cont (iter1, self1) =>
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_start1, h_end1, h_pn1, h_ic1, h_poly_lt, h_poly_idx_eq,
              p, h_px, h_py, h_update⟩ := h_cf
      refine ⟨⟨by rw [h_end1]; exact h_end',
              by grind, by grind,
              by rw [h_pn1]; exact h_pn',
              by rw [h_ic1]; exact h_ic', ?_,
              n + 1, Function.update selfs' (n + 1) self1,
              ?_, ?_, ?_, ?_⟩, by grind⟩
      · intro k hk
        have h_old := h_cap' k hk
        have h_len_le := body_pts_length_le self1 self' p
          ((chunk.index.val * 16 + iter'.start.val) % 16) h_update k
        rw [h_start1, h_end1, h_end_val]
        rw [h_end_val] at h_old
        grind
      · have h0 : (0 : Nat) ≠ n + 1 := by omega
        simp [h_s0]
      · simp [Function.update_self]
      · grind
      · intro j hj
        by_cases hj_lt : j < n
        · obtain ⟨pn_j, ic_j, h_poly_lt', h_poly_idx_eq', p', h_px', h_py', h_upd'⟩ :=
            h_chain j hj_lt
          have h1 : j ≠ n + 1 := by omega
          have h2 : j + 1 ≠ n + 1 := by omega
          simp only [Function.update_of_ne h1, Function.update_of_ne h2]
          exact ⟨pn_j, ic_j, h_poly_lt', h_poly_idx_eq', p', h_px', h_py', h_upd'⟩
        · have hj_eq : j = n := by omega
          subst hj_eq
          have hne : j ≠ j + 1 := by omega
          simp only [Function.update_of_ne hne, Function.update_self, h_sn]
          have h_i_eq : iter.start.val + j = iter'.start.val := by grind
          simp only [h_i_eq]
          refine ⟨by rw [h_pn1]; exact h_pn',
                  by rw [h_ic1]; exact h_ic',
                  h_poly_lt, h_poly_idx_eq,
                  p, h_px, h_py, h_update⟩
  · refine ⟨rfl, le_refl _, h_start_le, rfl, rfl, ?_,
            0, fun _ => self, rfl, rfl, by dsimp; omega, fun j hj => by omega⟩
    intro k hk
    grind

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop

/-! # Spec theorem for `spqr::encoding::polynomial::{impl Decoder for PolyDecoder}::add_chunk`

Processes a single 32-byte `Chunk` by iterating its 16 two-byte pairs (`i = 0 .. 15`), computing
`total_idx = chunk.index * 16 + i`, `poly = total_idx % 16`, `poly_idx = total_idx / 16`, and
building the point `Pt { x = GF16::new(poly_idx), y = GF16::new((data[2i] << 8) | data[2i+1]) }`.
If `poly_idx < necessary_points(i)` or the sorted set `pts[poly]` has fewer entries than
`necessary_points(i)`, the point is pushed onto `pts[poly]` via `SortedSet::push`; otherwise it
is discarded.

The by-value `add_chunk` introduces no additional logic beyond the delegation: it calls
`add_chunk_loop` with the fixed range `0..16`, so its postcondition is inherited from the
corresponding `loop_spec`.

Key invariants preserved:
- `pts_needed` is unchanged (matching the Rust `#[hax_lib::ensures]` annotation).
- `is_complete` is unchanged.

**Source**: spqr/src/encoding/polynomial.rs (lines 879:4-904:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk`**:

• Takes a `PolyDecoder` `self` and a `Chunk` `chunk` (a 32-byte buffer with a 16-bit chunk index).
• Delegates immediately to `add_chunk_loop` with the fixed range `{start := 0, end := 16}`:
    `add_chunk_loop { start := 0#usize, «end» := 16#usize } self chunk`
  which iterates over all 16 two-byte pairs in the chunk data.
• Returns the resulting `PolyDecoder` after conditionally inserting up to 16 points into the
  sorted sets `pts[0], …, pts[15]`.

• The function preserves `pts_needed` (matching the Rust ensures `future(self).pts_needed ==
  self.pts_needed`) and `is_complete`.
• The result is witnessed by a chain of 16 intermediate decoder states
  `selfs 0 = self, selfs 1, …, selfs 16 = result`, where each step `j` (`0 ≤ j < 16`) computes:
  - `total_idx = chunk.index * 16 + j`
  - `poly = total_idx % 16`
  - `poly_idx = total_idx / 16`
  - `x = GF16::new(poly_idx)`, `y = GF16::new((data[2j] << 8) + data[2j + 1])`
  and either leaves the decoder unchanged or pushes `Pt { x, y }` onto `pts[poly]` via
  `SortedSet::push`, with the same push semantics as `body_spec` (append, replace-last, or
  sorted-insert).

The proof unfolds `add_chunk` to expose the underlying `add_chunk_loop` call and applies the
already-registered `loop_spec` via `WP.spec_mono`, discharging the trivial preconditions
(`iter.end ≤ 16`, `iter.start ≤ iter.end`) with `scalar_tac` and propagating `h_overflow` and
`h_push_cap` to the loop spec's overflow/capacity requirements.

**Source**: spqr/src/encoding/polynomial.rs (lines 879:4-904:5)
-/
@[step]
theorem add_chunk_spec
    (self : PolyDecoder) (chunk : encoding.Chunk)
    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 → (self.pts[k]!).length + 17 ≤ Usize.max) :
    add_chunk self chunk ⦃ (result : PolyDecoder) =>
      result.pts_needed = self.pts_needed ∧
      result.is_complete = self.is_complete ∧
      ∃ (selfs : Nat → PolyDecoder),
        selfs 0 = self ∧
        selfs 16 = result ∧
        ∀ (j : Nat), j < 16 →
          let total_idx := chunk.index.val * 16 + j
          let poly := total_idx % 16
          let poly_idx := total_idx / 16
          (selfs (j + 1)).pts_needed = self.pts_needed ∧
          (selfs (j + 1)).is_complete = self.is_complete ∧
          poly < 16 ∧
          poly_idx = chunk.index.val ∧
          ∃ (p : Pt),
            p.x.value.val = poly_idx ∧
            p.y.value.val = (chunk.data[j * 2]!) * 256 + (chunk.data[j * 2 + 1]!) ∧
            (selfs (j + 1) = selfs j ∨
             ((∀ (k : Nat), k ≠ poly → (selfs (j + 1)).pts[k]! = (selfs j).pts.val[k]!) ∧
              match ((selfs j).pts.val[poly]!).val.getLast? with
              | none =>
                  ((selfs (j + 1)).pts.val[poly]!).val = ((selfs j).pts.val[poly]!).val ++ [p]
              | some last =>
                match Pt.Insts.CoreCmpOrd.cmp p last with
                | ok Ordering.gt =>
                    ((selfs (j + 1)).pts.val[poly]!).val = ((selfs j).pts.val[poly]!).val ++ [p]
                | ok Ordering.eq =>
                    ((selfs (j + 1)).pts.val[poly]!).val =
                    ((selfs j).pts.val[poly]!).val.dropLast ++ [p]
                | ok Ordering.lt =>
                    ∃ (m : Nat),
                      m ≤ ((selfs j).pts.val[poly]!).val.length ∧
                      (((selfs (j + 1)).pts.val[poly]!).val =
                          ((selfs j).pts.val[poly]!).val.take m ++ [p] ++
                          ((selfs j).pts.val[poly]!).val.drop m ∨
                       (m < ((selfs j).pts.val[poly]!).val.length ∧
                        ((selfs (j + 1)).pts.val[poly]!).val =
                          ((selfs j).pts.val[poly]!).val.take m ++ [p] ++
                          ((selfs j).pts.val[poly]!).val.drop (m + 1)))
                | _ => False)) ⦄ := by
  unfold add_chunk
  apply WP.spec_mono (add_chunk_loop.loop_spec chunk
    { start := 0#usize, «end» := 16#usize } self
    (by scalar_tac) (by scalar_tac) h_overflow
    (by intro k hk; have := h_push_cap k hk; grind))
  intro r ⟨h1, h2, s, h3, h4, _, h5⟩
  refine ⟨h1, h2, s, h3, h4, fun j hj => ?_⟩
  have h := h5 j hj
  simp only [show (0#usize : Usize).val = 0 from rfl, Nat.zero_add] at h
  exact h

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder
