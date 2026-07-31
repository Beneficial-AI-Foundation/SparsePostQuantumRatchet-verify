/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Aeneas.GF16New
import Spqr.Specs.Aeneas.RangeIteratorNext
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.NecessaryPoints
import Spqr.Specs.Encoding.Polynomial.Pt.Cmp

/-! # Spec theorem for `PolyDecoder::add_chunk`: loop body 0 -/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

private instance instInhabitedSortedSetPt : Inhabited (sorted_vec.SortedSet Pt) :=
  ⟨alloc.vec.Vec.new Pt⟩

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop

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

private theorem u8_shl8_mod_u16_size (b : U8) :
    b.val <<< 8 % U16.size = b.val * 256 := by
  have hb : b.val ≤ 255 := by scalar_tac
  rw [Nat.shiftLeft_eq]
  simp only [Nat.reducePow]
  apply Nat.mod_eq_of_lt
  have : U16.size = 65536 := by scalar_tac
  omega

set_option maxHeartbeats 8000000 in
-- heavy grind
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
          ∃ (p : Pt),
            p.x.value.val = poly_idx ∧
            p.y.value.val =
              (chunk.data.val[i * 2]!).val * 256 +
              (chunk.data.val[i * 2 + 1]!).val ∧
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
    split
    · -- Branch 1: poly_idx < necessary_points, push with hroom true
      step*
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
              · simp_all; scalar_tac
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
                · simp_all; scalar_tac
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
                  · simp_all; scalar_tac
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
          step*
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
                  Nat.add_left_cancel_iff, and_self, imp_self, UScalarTy.U16_numBits_eq,
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
                        simp_all
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
      step*
      have h_len := h_push_cap (↑iter.start % 16) (by omega)
      step*
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
                · simp_all; scalar_tac
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
                  · simp_all; scalar_tac
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
              . exact h_start1
              · constructor
                · exact h_end1
                · refine ⟨Pt.mk x y, ?_, ?_, ?_⟩
                  · simp_all
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
                    Nat.add_left_cancel_iff, and_self, imp_self, UScalarTy.U16_numBits_eq,
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
                          simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos,
                            Order.add_one_le_iff, not_true_eq_false, reduceCtorEq, false_and,
                            implies_true,  and_self,
                            UScalarTy.U16_numBits_eq, UScalarTy.Usize_numBits_eq,
                            System.Platform.sixteen_le_numBits,
                            UScalar.cast_val_mod_pow_greater_numBits_eq, UScalarTy.U8_numBits_eq,
                            Nat.reduceLeDiff, Bvify.U16.UScalar_bv, Bvify.UScalar.cast_bv,
                            Bvify.U8.UScalar_bv, UScalar.lt_equiv, not_lt, Nat.mul_add_mod_self_right,
                            alloc.vec.Vec.len, Usize.ofNatCore_val_eq, List.getElem!_eq_getElem?_getD,
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

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop
