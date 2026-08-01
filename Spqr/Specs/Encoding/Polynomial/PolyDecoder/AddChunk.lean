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

Each iteration builds an evaluation point from a two-byte pair and inserts it into the
polynomial's sorted set. Routing: `(chunk_index * 16 + i) % 16 = i` selects the polynomial,
`(chunk_index * 16 + i) / 16 = chunk_index` gives the x-coordinate. After all chunks,
each polynomial holds the `completePoints` format for Lagrange interpolation.

**Source**: spqr/src/encoding/polynomial.rs (lines 879:4–904:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

private instance instInhabitedSortedSetPt : Inhabited (sorted_vec.SortedSet Pt) :=
  ⟨alloc.vec.Vec.new Pt⟩

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop

/-- **Sorted insert totality**: `sortedInsert` always succeeds for any list, element, and starting
index. By induction on the list with case-split on comparison. Needed by `body_spec_0` to
discharge the `sortedInsert` branch. -/
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

/-- **Byte shift identity**: `b.val <<< 8 % U16.size = b.val * 256` for `U8`, since
`b.val * 256 ≤ 65280 < 65536`. -/
private theorem u8_shl8_mod_u16_size (b : U8) :
    b.val <<< 8 % U16.size = b.val * 256 := by
  have hb : b.val ≤ 255 := by scalar_tac
  rw [Nat.shiftLeft_eq]
  simp only [Nat.reducePow]
  apply Nat.mod_eq_of_lt
  have : U16.size = 65536 := by scalar_tac
  omega

/-! ## Lagrange polynomial identity properties -/

/-- **Chunk point routing**: when `i < 16`, `(chunk_index * 16 + i) % 16 = i` (polynomial index)
and `(chunk_index * 16 + i) / 16 = chunk_index` (x-coordinate). -/
private lemma chunk_point_routing (chunk_index i : Nat) (h : i < 16) :
    (chunk_index * 16 + i) % 16 = i ∧
    (chunk_index * 16 + i) / 16 = chunk_index := by
  constructor <;> omega

set_option maxHeartbeats 8000000 in
-- haevy grind
/-- **Spec theorem for `body` (base case)**:

On `done`: state unchanged, iterator exhausted. On `cont`: advances iterator, preserves
`pts_needed`/`is_complete`, builds point `p` from chunk data (x via division, y via big-endian
encoding), and either discards or inserts it into `pts[(chunk_index * 16 + i) % 16]`.

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
      · -- poly_idx < necessary_points, push (hroom true)
        split
        · -- getLast? = none
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
        · -- getLast? = some
          step*
          split
          · -- gt
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
          · -- eq
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
          · -- lt (sortedInsert)
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
      · -- overflow impossible (hroom false)
        step*
        have := h_push_cap (↑iter.start % 16) (by omega)
        grind
    · -- second push path (¬ poly_idx < np, len < np)
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
    · -- skip (self unchanged)
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

Strengthens `body_spec_base` with `poly < 16` and `poly_idx = chunk.index.val` via
`chunk_point_routing`. Downstream Lagrange identities are proved in the interpolation modules.

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

Iterates `body` over `[iter.start, iter.end)` using `loop.spec_decr_nat`. Each step builds
a point and conditionally pushes it onto `pts[poly]`. The invariant preserves iterator end,
`pts_needed`, `is_complete`, push capacity, and a chain of intermediate states.

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

Iterates over `[iter.start, iter.end)` with `iter.end ≤ 16`, preserving `pts_needed` and
`is_complete`. Witnesses via a chain `selfs 0 = self, …, selfs n = result` where each step
builds a point and conditionally pushes it onto the appropriate sorted set.

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

Processes a 32-byte `Chunk` by iterating its 16 two-byte pairs, building points and
conditionally pushing them onto `pts[poly]`. Delegates to `add_chunk_loop` with range `0..16`.
Preserves `pts_needed` and `is_complete`.

**Source**: spqr/src/encoding/polynomial.rs (lines 879:4-904:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk`**:

Delegates to `add_chunk_loop` with range `0..16`. Preserves `pts_needed` and `is_complete`.
Witnessed by 16 intermediate states, each building a point and conditionally pushing it onto
the appropriate sorted set. Proof via `WP.spec_mono` on `loop_spec`.

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
