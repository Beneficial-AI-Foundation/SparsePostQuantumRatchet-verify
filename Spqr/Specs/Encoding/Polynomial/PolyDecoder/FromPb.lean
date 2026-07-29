/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.ModByMonic
import Spqr.Specs.Aeneas.RangeIteratorNext
import Spqr.Math.List
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Polynomial.Pt.Deserialize
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.IntoPb

/-!
# Spec theorem for `PolyDecoder::from_pb`: loop body 1

One step of the inner point-deserialization loop. Given `pts : Vec<u8>`, a sorted set `v`, and
cursor `j`, the body either terminates (fewer than 4 bytes left) or reads a 4-byte big-endian
chunk, deserializes it into a `Pt` over GF(2¹⁶), pushes the point onto `v`, and advances `j`
by 4.

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyDecoder.from_pb_loop0_loop0

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.from_pb_loop0_loop0.body`**:

One step of the inner 4-byte-chunk deserialization loop. Decides between termination
(insufficient bytes) and a single decode + push step.

• **done** (`pts.len() < j + 4`): returns `v` unchanged.
• **cont** (`j + 4 ≤ pts.len()`): decodes the next 4 bytes into a `Pt` via big-endian
  two-byte pairs, pushes it onto the sorted set, and advances `j` by 4. -/
@[step]
theorem body_spec
    (pts : alloc.vec.Vec U8)
    (v : sorted_vec.SortedSet Pt)
    (j : Usize)
    (h_j_overflow : j + 4 ≤ Usize.max)
    (h_v_push : v.length + 1 ≤ Usize.max) :
    body pts v j ⦃ cf =>
      match cf with
      | ControlFlow.done v' =>
          v' = v ∧ pts.length < j.val + 4
      | ControlFlow.cont (v', j') =>
          j + 4 ≤ pts.length ∧
          j' = j.val + 4 ∧
          ∃ (p : Pt),
            p.x.value.val = 256 * pts[j]!  + pts[j.val + 1]! ∧
            p.y.value.val = 256 * pts[j.val + 2]! + pts[j.val + 3]! ∧
            v'.val = v.val ++ [p] ⦄ := by
  unfold body
  step*
  simp_all only [alloc.vec.Vec.length, Order.add_one_le_iff, Array.getElem!_Nat_eq,
    List.Vector.length_val, UScalar.ofNatCore_val_eq, Nat.ofNat_pos, getElem!_pos, Nat.one_lt_ofNat,
    Nat.reduceLT, Nat.lt_add_one, true_and]
  constructor
  · grind
  · use p
    have hv : v.length < Usize.max := by omega
    have h0 : j < pts.length := by scalar_tac
    have h1 : j + 1 < pts.length := by scalar_tac
    have h2 : j + 2 < pts.length := by scalar_tac
    have h3 : j + 3 < pts.length := by scalar_tac
    have h_push := sorted_vec.SortedSet.push_spec Pt.Insts.CoreCmpOrd v p (by scalar_tac)
    simp_all [Array.make, List.getElem_cons_zero, List.getElem_cons_succ,
      sorted_vec.SortedSet.push, UScalarTy.Usize_numBits_eq]
    grind

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.from_pb_loop0_loop0`**:

Full inner deserialization loop. Returns a chain of `n` decode-and-append steps consuming all
complete 4-byte chunks from `pts`, with `vs 0 = v` and `vs n = v_result`.

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem loop_spec
    (pts : alloc.vec.Vec U8)
    (v : sorted_vec.SortedSet Pt)
    (j : Usize)
    (h_j_overflow : j + 4 ≤ Usize.max)
    (h_pts_overflow : pts.length + 4 ≤ Usize.max)
    (h_j_le_pts : j ≤ pts.length)
    (h_v_room : v.length + pts.length + 1 ≤ Usize.max) :
    from_pb_loop0_loop0 pts v j ⦃ (v_result : sorted_vec.SortedSet Pt) =>
      ∃ (n : Nat) (vs : Nat → sorted_vec.SortedSet Pt),
        vs 0 = v ∧ vs n = v_result ∧
        j + 4 * n ≤ pts.length ∧
        pts.length < j + 4 * (n + 1) ∧
        ∀ (k : Nat), k < n →
          ∃ (p : Pt),
            p.x.value.val = 256 * pts[j + 4 * k]! + pts[j + 4 * k + 1]! ∧
            p.y.value.val = 256 * pts[j + 4 * k + 2]! + pts[j + 4 * k + 3]! ∧
            (vs (k + 1)).val = (vs k).val ++ [p] ⦄ := by
  unfold from_pb_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : sorted_vec.SortedSet Pt × Usize) =>
                  pts.val.length + 4 - p.2.val)
    (inv := fun (p : sorted_vec.SortedSet Pt × Usize) =>
        let v' := p.1
        let j' := p.2
        j'.val + 4 ≤ Usize.max ∧
        v'.val.length + (pts.val.length - j'.val) + 1 ≤ Usize.max ∧
        (∃ (n : Nat) (vs : Nat → sorted_vec.SortedSet Pt),
          vs 0 = v ∧ vs n = v' ∧
          j'.val = j.val + 4 * n ∧
          j'.val ≤ pts.val.length ∧
          ∀ (k : Nat), k < n →
            ∃ (p : Pt),
              p.x.value.val =
                (pts.val[j.val + 4 * k]!).val * 256 +
                (pts.val[j.val + 4 * k + 1]!).val ∧
              p.y.value.val =
                (pts.val[j.val + 4 * k + 2]!).val * 256 +
                (pts.val[j.val + 4 * k + 3]!).val ∧
              (vs (k + 1)).val = (vs k).val ++ [p]))
  · rintro ⟨v', j'⟩ ⟨h_overflow', h_v_room', n, vs, h_v0, h_vn, h_jn, h_j_le, h_chain⟩
    simp only  at h_overflow' h_v_room' h_v0 h_vn h_jn h_j_le h_chain ⊢
    have h_body := body_spec pts v' j' (by omega) (by grind)
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done v_final =>
      simp only  at h_cf ⊢
      obtain ⟨h_v_eq, h_not_enough⟩ := h_cf
      subst h_v_eq
      exact ⟨n, vs, h_v0, h_vn, by grind, by grind, by grind⟩
    | ControlFlow.cont (v'', j'') =>
      simp only  at h_cf ⊢
      obtain ⟨h_enough, h_j_eq, p, h_px, h_py, h_vpush⟩ := h_cf
      refine ⟨⟨by grind, ?_,
              n + 1,
              Function.update vs (n + 1) v'',
              ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · have h_len : v''.val.length = v'.val.length + 1 := by
          rw [h_vpush]; simp
        grind
      · have h0 : (0 : Nat) ≠ n + 1 := by omega
        simp_all
      · simp
      · omega
      · grind
      · intro k hk
        by_cases hk_lt : k < n
        · obtain ⟨p', h_px', h_py', h_vpush'⟩ := h_chain k hk_lt
          refine ⟨p', h_px', h_py', ?_⟩
          have h1 : k ≠ n + 1 := by omega
          have h2 : k + 1 ≠ n + 1 := by omega
          simp_all
        · have hk_eq : k = n := by omega
          subst hk_eq
          refine ⟨p, by grind, by grind, by grind⟩
      · omega
  · refine ⟨by omega, by (simp only ; grind), 0, fun _ => v, rfl, rfl, by grind, by omega, ?_⟩
    intro k hk
    omega

end spqr.encoding.polynomial.PolyDecoder.from_pb_loop0_loop0

/-! # Spec theorem for `PolyDecoder::from_pb`: loop body 0

One step of the outer loop. Given `v : Vec<Vec<u8>>`, a range iterator over slot indices, and
`out_pts : [SortedSet<Pt>; 16]`, the body advances the iterator and either terminates (done)
or deserializes slot `i` by allocating a fresh `SortedSet`, running the inner 4-byte loop on
`v[i]`, and storing the result into `out_pts[i]`.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyDecoder.from_pb_loop0

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.from_pb_loop0.body`**:

One step of the outer loop. Either terminates (iterator exhausted, `out_pts` unchanged) or
deserializes `v[i]` via the inner 4-byte loop and stores the result into `out_pts[i]`.

The cont case provides a chain of append operations for the decoded points from
`v[i]`, with big-endian 4-byte decoding of each `Pt`. -/
@[step]
theorem body_spec
    (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (iter : core.ops.range.Range Usize)
    (out_pts : Array (sorted_vec.SortedSet Pt) 16#usize)
    (h_end_le_v : iter.end ≤ v.length)
    (h_end_le_16 : iter.end.val ≤ 16)
    (h_pts_overflow : ∀ (j : Nat), j < v.length → (v[j]!).length + 4 ≤ Usize.max) :
    body v iter out_pts ⦃ cf =>
      match cf with
      | ControlFlow.done out_pts' =>
          out_pts' = out_pts ∧ ¬(iter.start < iter.end)
      | ControlFlow.cont (iter1, out_pts') =>
          iter.start < iter.end ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          ∃ (v_final : sorted_vec.SortedSet Pt) (n : Nat)
            (vs : Nat → sorted_vec.SortedSet Pt),
            out_pts'.val[iter.start.val]! = v_final ∧
            (∀ (k : Nat), k ≠ iter.start →
              out_pts'.val[k]! = out_pts.val[k]!) ∧
            vs n = v_final ∧
            4 * n ≤ (v[iter.start]!).length ∧
            (v[iter.start.val]!).length < 4 * (n + 1) ∧
            ∀ (k : Nat), k < n →
              ∃ (p : Pt),
                p.x.value.val =
                  256 * ((v[iter.start.val]!)[4 * k]!) + (v[iter.start.val]!)[4 * k + 1]! ∧
                p.y.value.val =
                  256 * (v[iter.start.val]!)[4 * k + 2]! + (v[iter.start.val]!)[4 * k + 3]! ∧
                (vs (k + 1)).val = (vs k).val ++ [p] ⦄ := by
  unfold body
  obtain ⟨⟨opt, iter1'⟩, hnext, h_none, h_some⟩ :=
    WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_spec' iter)
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.len, UScalar.lt_equiv,
      UScalar.ofNatCore_val_eq, uncurry_apply_pair, not_lt, ↓existsAndEq,
      List.getElem!_eq_getElem?_getD, ne_eq, exists_and_left, true_and]
    have h_i_lt_v : iter.start.val < v.val.length := by grind
    have h_i_lt_16 : iter.start.val < 16 := by omega
    have h_pts_ov := h_pts_overflow iter.start.val h_i_lt_v
    simp only [sorted_vec.SortedSet.with_capacity]
    step*
    · simp_all only [true_and]
      grind
    · simp_all only [true_and]
      grind
    · simp_all only [not_true_eq_false, reduceCtorEq,
      false_and, implies_true, and_self, Usize.ofNatCore_val_eq,
      zero_add, Array.set_val_eq,
      List.set_getElem_self, Nat.not_eq, ne_eq, not_false_eq_true, lt_or_lt_iff_ne, true_or,
      or_true, List.set_getElem?_neq, List.length_set, List.Vector.length_val,
      UScalar.ofNatCore_val_eq, getElem?_pos, List.getElem_set_self, Option.getD_some, true_and]
      rename_i ha hb hc hd he hf hg
      use v2
      exact ⟨hc, v2_post2, by grind, by grind, by grind⟩
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.from_pb_loop0`**:

Full outer loop. For every slot `j < iter.end.val`, the result array contains a sorted set
produced by a chain of `n` decode-and-append steps consuming all complete 4-byte chunks from
`v[j]`.

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem loop_spec
    (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (out_pts : Array (sorted_vec.SortedSet Pt) 16#usize)
    (h_end_le_v : iter.end ≤ v.length)
    (h_end_le_16 : iter.end.val ≤ 16)
    (h_start_le : iter.start ≤ iter.end)
    (h_pts_overflow : ∀ (j : Nat), j < v.length → (v[j]!).length + 4 ≤ Usize.max)
    (h_pre : ∀ (j : Nat), j < iter.start →
        ∃ (v_final : sorted_vec.SortedSet Pt) (n : Nat)
          (vs : Nat → sorted_vec.SortedSet Pt),
          out_pts.val[j]! = v_final ∧
          vs n = v_final ∧
          4 * n ≤ (v.val[j]!).val.length ∧
          (v.val[j]!).val.length < 4 * (n + 1) ∧
          ∀ (k : Nat), k < n →
            ∃ (p : Pt),
              p.x.value.val = ((v[j]!)[4 * k]!) * 256 + ((v[j]!)[4 * k + 1]!) ∧
              p.y.value.val = ((v[j]!)[4 * k + 2]!) * 256 + ((v[j]!)[4 * k + 3]!) ∧
              (vs (k + 1)).val = (vs k).val ++ [p]) :
    from_pb_loop0 iter v out_pts ⦃ (result : Array (sorted_vec.SortedSet Pt) 16#usize) =>
      ∀ (j : Nat), j < iter.end →
        ∃ (v_final : sorted_vec.SortedSet Pt) (n : Nat)
          (vs : Nat → sorted_vec.SortedSet Pt),
          result.val[j]! = v_final ∧
          vs n = v_final ∧
          4 * n ≤ (v[j]!).length ∧
          (v[j]!).length < 4 * (n + 1) ∧
          ∀ (k : Nat), k < n →
            ∃ (p : Pt),
              p.x.value.val = (v[j]!)[4 * k]! * 256 + (v[j]!).val[4 * k + 1]! ∧
              p.y.value.val = (v[j]!)[4 * k + 2]! * 256 + (v[j]!)[4 * k + 3]! ∧
              (vs (k + 1)).val = (vs k).val ++ [p] ⦄ := by
  unfold from_pb_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize ×
                       Array (sorted_vec.SortedSet Pt) 16#usize) => p.1.end - p.1.start)
    (inv := fun (p : core.ops.range.Range Usize ×
                     Array (sorted_vec.SortedSet Pt) 16#usize) =>
        p.1.end = iter.end ∧
        iter.start.val ≤ p.1.start.val ∧
        p.1.start.val ≤ p.1.end.val ∧
        (∀ (j : Nat), j < p.1.start.val →
          ∃ (v_final : sorted_vec.SortedSet Pt) (n : Nat)
            (vs : Nat → sorted_vec.SortedSet Pt),
            p.2.val[j]! = v_final ∧
            vs n = v_final ∧
            4 * n ≤ (v.val[j]!).val.length ∧
            (v.val[j]!).val.length < 4 * (n + 1) ∧
            ∀ (k : Nat), k < n →
              ∃ (p : Pt),
                p.x.value.val = (v[j]!)[4 * k]! * 256 + (v[j]!)[4 * k + 1]! ∧
                p.y.value.val = (v[j]!)[4 * k + 2]! * 256 + (v[j]!)[4 * k + 3]! ∧
                (vs (k + 1)).val = (vs k).val ++ [p]))
  · rintro ⟨iter', out_pts'⟩ ⟨h_end', h_orig_le, h_start_le', h_inv'⟩
    simp only  at h_end' h_orig_le h_start_le' h_inv' ⊢
    have h_end_val : iter'.end.val = iter.end.val := by rw [h_end']
    have h_end_le_v' : iter'.end.val ≤ v.val.length := by grind
    have h_end_le_16' : iter'.end.val ≤ 16 := by omega
    have h_body := body_spec v iter' out_pts' h_end_le_v' h_end_le_16' h_pts_overflow
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done out_pts'' =>
      simp only  at h_cf ⊢
      obtain ⟨h_out_eq, h_not_lt⟩ := h_cf
      subst h_out_eq
      intro j hj
      exact h_inv' j (by grind)
    | ControlFlow.cont (iter'', out_pts'') =>
      simp only  at h_cf ⊢
      obtain ⟨h_lt, h_start1, h_end1, v_final, n, vs,
              h_slot, h_other, h_vs_n, h_n_lo, h_n_hi, h_chain⟩ := h_cf
      have h_end1_val : iter''.end.val = iter'.end.val := by rw [h_end1]
      refine ⟨⟨by rw [h_end1]; exact h_end',
              by omega,
              by grind,
              fun j hj => ?_⟩,
              by grind⟩
      by_cases hj_lt : j < iter'.start.val
      · obtain ⟨vf, nn, vss, h_slot', h_vs_nn, h_nn_lo, h_nn_hi, h_chain'⟩ :=
          h_inv' j hj_lt
        refine ⟨vf, nn, vss, ?_, h_vs_nn, h_nn_lo, h_nn_hi, h_chain'⟩
        have hj_ne : j ≠ iter'.start.val := by omega
        rw [← h_slot']
        grind
      · have hj_eq : j = iter'.start.val := by omega
        subst hj_eq
        exact ⟨v_final, n, vs, h_slot, h_vs_n, h_n_lo, h_n_hi, by grind⟩
  · exact ⟨rfl, le_refl _, h_start_le, h_pre⟩

end spqr.encoding.polynomial.PolyDecoder.from_pb_loop0

/-!
# Spec theorem for `spqr::encoding::polynomial::{PolyDecoder}::from_pb`

Reconstructs a `PolyDecoder` from its protobuf representation. Validates `pb.pts.len() == 16`
and `len() % 4 == 0` for each slot, then deserializes all 16 slots of big-endian 4-byte chunks
into `[SortedSet<Pt>; 16]`, and casts `pb.pts_needed : u32` to `usize`.

**Source**: spqr/src/encoding/polynomial.rs (lines 815:4-854:5)
-/

open Aeneas Aeneas.Std Result spqr.math.gf spqr.encoding.polynomial

namespace spqr.encoding.polynomial.PolyDecoder

set_option maxHeartbeats 4000000 in
-- heavy simp
/-- **Spec theorem for `encoding.polynomial.PolyDecoder.from_pb`** (byte-level):

Tri-branch postcondition: (1) bad length → `Err`, (2) bad chunking → `Err`, (3) valid →
`Ok decoder` with `pts_needed`, `is_complete` preserved and per-slot chain witnesses for the
decoded points.

`SortedSet.with_capacity` is now a concrete definition (returns empty set).

**Source**: spqr/src/encoding/polynomial.rs (lines 815:4-854:5)
-/
theorem from_pb_spec
    (pb : proto.pq_ratchet.PolynomialDecoder)
    (h_pts_overflow : ∀ (j : Nat), j < pb.pts.length →
        (pb.pts[j]!).length + 4 ≤ Usize.max) :
    from_pb pb ⦃ (result : core.result.Result
        encoding.polynomial.PolyDecoder
        encoding.polynomial.PolynomialError) =>
      -- Bad length: returns Err
      (pb.pts.val.length ≠ 16 →
        result = core.result.Result.Err
          encoding.polynomial.PolynomialError.SerializationInvalid) ∧
      -- Bad chunking: some slot has length not a multiple of 4
      (pb.pts.val.length = 16 →
        (∃ (j : Nat), j < 16 ∧ (pb.pts.val[j]!).val.length % 4 ≠ 0) →
        result = core.result.Result.Err
          encoding.polynomial.PolynomialError.SerializationInvalid) ∧
      -- Valid: every slot has length a multiple of 4, result is Ok with chain witnesses
      (pb.pts.val.length = 16 →
        (∀ (j : Nat), j < 16 → (pb.pts.val[j]!).val.length % 4 = 0) →
        match result with
        | core.result.Result.Ok decoder =>
          decoder.pts_needed.val = pb.pts_needed.val ∧
          decoder.is_complete = pb.is_complete ∧
          decoder.pts.val.length = 16 ∧
          ∀ (j : Nat), j < 16 →
            ∃ (v_final : sorted_vec.SortedSet Pt) (n : Nat)
              (vs : Nat → sorted_vec.SortedSet Pt),
              decoder.pts.val[j]! = v_final ∧
              vs n = v_final ∧
              4 * n ≤ (pb.pts[j]!).length ∧
              (pb.pts[j]!).length < 4 * (n + 1) ∧
              ∀ (k : Nat), k < n →
                ∃ (p : Pt),
                  p.x.value.val = (pb.pts[j]!)[4 * k]! * 256 + (pb.pts.val[j]!)[4 * k + 1]! ∧
                  p.y.value.val = (pb.pts[j]!)[4 * k + 2]!* 256 + (pb.pts[j]!)[4 * k + 3]! ∧
                  (vs (k + 1)).val = (vs k).val ++ [p]
        | core.result.Result.Err _ => False) ⦄ := by
  unfold from_pb
  simp only [alloc.vec.Vec.len, bne_iff_ne, ne_eq, UScalar.neq_to_neq_val, Usize.ofNatCore_val_eq,
    UScalar.ofNatCore_val_eq, alloc.vec.Vec.index_slice_index, sorted_vec.SortedSet.new, bind_tc_ok,
    ite_not, List.getElem!_eq_getElem?_getD, forall_exists_index, and_imp, List.Vector.length_val,
    ↓existsAndEq, alloc.vec.Vec.length, alloc.vec.Vec.getElem!_Nat_eq, true_and]
  step*
  · simp_all only [alloc.vec.Vec.length, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos,
    Usize.ofNatCore_val_eq, ReduceNat.reduceNatEq, ↓existsAndEq, List.Vector.length_val,
    UScalar.ofNatCore_val_eq, List.getElem!_eq_getElem?_getD, true_and, not_true_eq_false,
    reduceCtorEq, imp_self, getElem?_pos, Option.getD_some, imp_false, Decidable.not_not,
    UScalarTy.U32_numBits_eq, UScalarTy.Usize_numBits_eq, System.Platform.le_numBits,
    UScalar.cast_val_mod_pow_greater_numBits_eq, implies_true, and_self, and_true]
    intro x hx
    interval_cases x <;> assumption
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind
  · simp_all
    grind

end spqr.encoding.polynomial.PolyDecoder
