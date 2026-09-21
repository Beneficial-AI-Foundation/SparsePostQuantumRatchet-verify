/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.NUM_POLYS
import Spqr.Specs.Encoding.Polynomial.Poly.Zero
import Spqr.Specs.Encoding.Polynomial.Poly.Deserialize
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.IntoPb
/-! # Spec theorem for `PolyEncoder::from_pb`: loop body 0

One step of the outer polynomial-deserialization loop. Advances the range iterator and either:
1. **Done**: iterator exhausted → returns `Ok(PolyEncoder { idx: i, s: Polys(out) })`.
2. **Continue**: deserializes `v[j]` into a `Poly` via `Poly::deserialize` and updates `out[j]`.

Each coefficient satisfies the big-endian invariant:
`value = serialized[2*k] * 256 + serialized[2*k+1]`.

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf spqr.math.gf

namespace spqr.encoding.polynomial.PolyEncoder.from_pb_loop0

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.from_pb_loop0.body`**:

One step of the outer deserialization loop. Retrieves the next index `j` and either terminates
(wrapping output as `Ok(PolyEncoder { idx := i, s := Polys out })`) or deserializes `v[j]`
into a `Poly` and updates `out[j]`.

• **done**: `¬ (iter.start < iter.end)`, result wraps the current output.
• **cont**: iterator advances by one; `out'[j]` has degree `(v[j]!).length / 2` and each
  coefficient `k` satisfies `value = 256 * v[j][2*k] + v[j][2*k+1]`. -/
@[step]
theorem body_spec
    (i : U32) (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (iter : core.ops.range.Range Usize) (out : Array Poly 16#usize)
    (h_end_le_v : iter.end ≤ v.length)
    (h_end_le_16 : iter.end.val ≤ 16)
    (h_nonempty : ∀ j < v.length, (v[j]!).length ≠ 0)
    (h_even : ∀ j < v.length, (v[j]!).length % 2 = 0) :
    body i v iter out ⦃ cf =>
      match cf with
      | ControlFlow.done result =>
          result = .Ok { idx := i, s := EncoderState.Polys out } ∧
          ¬(iter.start < iter.end)
      | ControlFlow.cont (iter1, out') =>
          iter.start < iter.end ∧
          iter1.start = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
            (∀ k ≠ iter.start, out'[k]! = out[k]!) ∧
            (out'[iter.start]!).degree = (v[iter.start]!).length / 2 ∧
            (∀ k < (v[iter.start]!).length / 2,
                ((out'[iter.start]!).coefficients[k]!).value.val =
                  256 * (v[iter.start]!)[2 * k]!  + (v[iter.start]!)[2 * k + 1]!) ⦄ := by
  unfold body
  obtain ⟨⟨opt, iter1'⟩, hnext, h_none, h_some⟩ :=
    WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_spec' iter)
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.end.val
  · step*
    · simp_all [alloc.vec.Vec.deref]
    · simp_all [alloc.vec.Vec.deref]
    · simp_all only [ne_eq, List.length_eq_zero_iff,
        not_true_eq_false, reduceCtorEq, false_and, implies_true,
          true_and]
      have hderef : ∀ (w : alloc.vec.Vec U8), w.deref = w := fun _ => rfl
      simp [*]
      grind
    · cases r <;> simp_all
  · grind

/-! # Spec theorem for `PolyEncoder::from_pb`: loop 0

The outer polynomial-deserialization loop. Repeatedly invokes the loop body to deserialize each
`v[j]` into a `Poly` and store it in the output array.

**Loop invariant**: `iter'.end = iter.end`, `iter'.start ≤ iter'.end`, and for all
`j < iter'.start`, `out'[j]` is the deserialized form of `v[j]` (big-endian byte-pair decoding).

At termination, the output array contains fully deserialized polynomials for `v[0..iter.end]`.
Proved by lifting `body_spec` through `loop.spec_decr_nat` with measure `iter.end - iter.start`.

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem loop_spec
    (i : U32)
    (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (iter : core.ops.range.Range Usize)
    (out : Array Poly 16#usize)
    (h_end_le_v : iter.end ≤ v.length)
    (h_end_le_16 : iter.end.val ≤ 16)
    (h_start_le : iter.start ≤ iter.end)
    (h_nonempty : ∀ j < v.length, (v[j]!).length ≠ 0)
    (h_even : ∀ j < v.length, (v[j]!).length % 2 = 0)
    (h_pre : ∀ j < iter.start, (out[j]!).degree = (v[j]!).length / 2 ∧
      ∀ k < (v[j]!).length / 2,
          ((out[j]!).coefficients[k]!).value.val = 256 * (v[j]!)[2 * k]! + (v[j]!)[2 * k + 1]!) :
    from_pb_loop0 iter i v out ⦃ (result : core.result.Result PolyEncoder PolynomialError) =>
      match result with
      | core.result.Result.Ok encoder =>
          encoder.idx = i ∧
          match encoder.s with
          | EncoderState.Polys out' =>
              ∀ j < iter.end, (out'[j]!).degree = (v[j]!).length / 2 ∧
              ∀ k < (v[j]!).length / 2,
              ((out'[j]!).coefficients[k]!).value.val = 256 * (v[j]!)[2 * k]! + (v[j]!)[2 * k + 1]!
          | _ => False
      | core.result.Result.Err _ => False ⦄ := by
  unfold from_pb_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × Array Poly 16#usize) => p.1.end - p.1.start)
    (inv := fun (p : core.ops.range.Range Usize × Array Poly 16#usize) =>
        p.1.end = iter.end ∧
        p.1.start ≤ p.1.end ∧
        (∀ j < p.1.start, (p.2[j]!).degree = (v[j]!).length / 2 ∧
          ∀ k < (v[j]!).length / 2,
            ((p.2[j]!).coefficients[k]!).value.val = 256 * (v[j]!)[2 * k]! + (v[j]!)[2 * k + 1]!))
  · rintro ⟨iter', out'⟩ ⟨h_end', h_start_le', h_pre'⟩
    simp only at h_end' h_start_le' h_pre' ⊢
    have h_end_val : iter'.end = iter.end := by rw [h_end']
    have h_body := body_spec i v iter' out' (by rw [h_end']; exact h_end_le_v) (by grind)
      h_nonempty h_even
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done result => grind
    | ControlFlow.cont (iter'', out'') =>
      simp only at h_cf ⊢
      obtain ⟨h_lt, h_start1, h_end1, h_out_preserve, h_degree, h_encode⟩ := h_cf
      constructor
      · refine ⟨by rw [h_end1]; exact h_end',
               by grind,
               fun j hj => ?_⟩
        by_cases hj_lt : j < iter'.start
        · obtain ⟨h_deg', h_enc'⟩ := h_pre' j hj_lt
          have hj_eq : j ≠  iter'.start := by grind
          have h_eq : out''[j]! = out'[j]! :=
            h_out_preserve ⟨j, by grind⟩ hj_eq
          exact ⟨by rw [h_eq]; exact h_deg', fun k hk => by rw [h_eq]; exact h_enc' k hk⟩
        · have hj_eq : j = iter'.start := by grind
          subst hj_eq
          exact ⟨h_degree, h_encode⟩
      · grind
  · exact ⟨rfl, h_start_le, h_pre⟩

end spqr.encoding.polynomial.PolyEncoder.from_pb_loop0

/-! # Spec theorem for `PolyEncoder::from_pb`: loop body 2

One step of the inner byte-deserialization loop (Points branch). Advances the range iterator
and either:
1. **Done**: iterator exhausted → loop terminates.
2. **Continue**: reads `pts[2*k]` and `pts[2*k+1]`, converts to `u16` via big-endian decoding,
   wraps as `GF16::new`, and pushes onto `v`.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyEncoder.from_pb_loop1_loop0

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.from_pb_loop1_loop0.body`**:

One step of the inner byte-deserialization loop. Given serialized byte vector `pts`, a range
iterator over `0..(pts.len() / 2)`, and output vector `v` of `GF16` values:

• **done**: `¬ (iter.start < iter.end)`, output unchanged.
• **cont**: iterator advances by one; `v` is extended by one `GF16` element whose value is
  `pts[2*k] * 256 + pts[2*k+1]` (big-endian reconstruction). -/
@[step]
theorem body_spec
    (pts : alloc.vec.Vec U8)
    (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec GF16)
    (h_end_le : 2 * iter.end ≤ pts.length)
    (h_start_le : iter.start.val ≤ iter.end.val)
    (h_overflow : v.val.length + (iter.end.val - iter.start.val) ≤ Usize.max) :
    body pts iter v ⦃ cf =>
      match cf with
      | ControlFlow.done v_final =>
          ¬(iter.start < iter.end) ∧
          v_final = v
      | ControlFlow.cont (iter1, v1) =>
          iter.start.val < iter.end.val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          ∃ (g : GF16),
            v1 = v ++ [g] ∧
            g.value.val = pts[2 * iter.start.val]! * 256 + pts[2 * iter.start.val + 1]! ⦄ := by
  unfold body
  obtain ⟨⟨opt, iter1'⟩, hnext, h_none, h_some⟩ :=
    WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_spec' iter)
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_2k_lt : 2 * iter.start < pts.length := by grind
    have h_2k1_lt : 2 * iter.start + 1 < pts.length := by grind
    have h_v_overflow : v.val.length + 1 ≤ Usize.max := by omega
    step*
    exact ⟨h_lt, h_start1, h_end1, g, v1_post, by simp_all [Array.make, Nat.mul_comm]⟩
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨h_lt, rfl⟩


/-! # Spec theorem for `PolyEncoder::from_pb`: loop 2

The inner byte-deserialization loop (Points branch). Repeatedly invokes the loop body to
reconstruct GF(2¹⁶) elements from byte pairs in `pts`.

**Loop invariant**: `v'.length = v.length + (iter'.start - iter.start)`, original prefix
preserved, and each new element at index `j` satisfies
`value = pts[2*j] * 256 + pts[2*j+1]`.

At termination, the output vector contains all deserialized GF(2¹⁶) elements.
Proved by lifting `body_spec` through `loop.spec_decr_nat` with measure `iter.end - iter.start`.

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem loop_spec
    (iter : core.ops.range.Range Usize)
    (pts : alloc.vec.Vec U8)
    (v : alloc.vec.Vec GF16)
    (h_end_le : 2 * iter.end ≤ pts.val.length)
    (h_start_le : iter.start ≤ iter.end)
    (h_overflow : v.length + (iter.end - iter.start) ≤ Usize.max) :
    from_pb_loop1_loop0 iter pts v ⦃ (v_result : alloc.vec.Vec GF16) =>
      v_result.length = v.length + (iter.end - iter.start) ∧
      (∀ (j : Nat), j < v.length → v_result[j]! = v[j]!) ∧
      ∀ (j : Nat), iter.start ≤ j → j < iter.end →
        (v_result[v.length + (j - iter.start)]!).value.val =
          pts[2 * j]! * 256 + pts[2 * j + 1]! ⦄ := by
  unfold from_pb_loop1_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × alloc.vec.Vec GF16) => p.1.end - p.1.start)
    (inv := fun (p : core.ops.range.Range Usize × alloc.vec.Vec GF16) =>
        p.1.end = iter.end ∧
        iter.start ≤ p.1.start ∧
        p.1.start ≤ p.1.end ∧
        p.2.val.length = v.val.length + (p.1.start.val - iter.start) ∧
        (∀ (j : Nat), j < v.length → p.2.val[j]? = v.val[j]?) ∧
        (∀ (j : Nat), iter.start ≤ j → j < p.1.start →
        p.2[v.length + (j - iter.start)]!.value.val = pts[2 * j]! * 256 + pts[2 * j + 1]!))
  · rintro ⟨iter', v'⟩ ⟨h_end', h_start_ge, h_start_le', h_len', h_prefix', h_pre'⟩
    simp only [] at h_end' h_start_ge h_start_le' h_len' h_prefix' h_pre' ⊢
    have h_end_val : iter'.end.val = iter.end.val := by rw [h_end']
    have h_body := body_spec pts iter' v' (by grind) (by grind) (by grind)
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done v_final => grind
    | ControlFlow.cont (iter'', v'') =>
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_start1, h_end1, g, h_v_eq, h_g_val⟩ := h_cf
      have h_end1_val : iter''.end.val = iter'.end.val := by rw [h_end1]
      constructor
      · refine ⟨by rw [h_end1]; exact h_end',
               by grind,
               by grind,
               by rw [h_v_eq]; simp [h_len']; grind,
               fun j hj => ?_,
               fun j hj1 hj2 => ?_⟩
        · rw [h_v_eq, getElem?_append_of_lt _ _ (by grind)]
          exact h_prefix' j hj
        · grind
      · omega
  · exact ⟨rfl, le_refl _, h_start_le, by simp, fun _ _ => rfl,
           fun _ h1 h2 => absurd h2 (by simp at h2 ⊢; omega)⟩

end spqr.encoding.polynomial.PolyEncoder.from_pb_loop1_loop0

/-! # Spec theorem for `PolyEncoder::from_pb`: loop body 1

One step of the outer point-deserialization loop (Points branch). Advances the range iterator
and either:
1. **Done**: iterator exhausted → returns `Ok(PolyEncoder { idx: i, s: Points(out) })`.
2. **Error**: byte vector has odd length → returns `Err(SerializationInvalid)`.
3. **Continue**: runs the inner loop to reconstruct GF(2¹⁶) elements from byte pairs, constructs
   a `Point`, and stores it in `out[j]`.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyEncoder.from_pb_loop1

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.from_pb_loop1.body`**:

One step of the outer point-deserialization loop. Retrieves the next index `j` and either
terminates (wrapping output as `Ok(PolyEncoder { idx := i, s := Points out })`) or deserializes
`v[j]` into a `Point` via inner byte-pair loop and updates `out[j]`.

• **done**: `¬ (iter.start < iter.end)`, result wraps current output.
• **cont**: iterator advances by one; `out'[j]` has `pt.value.length = v[j].length / 2` and each
  element `k` satisfies `value = v[j][2*k] * 256 + v[j][2*k+1]`. -/
@[step]
theorem body_spec
    (i : U32)
    (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (iter : core.ops.range.Range Usize)
    (out : Array Point 16#usize)
    (h_end_le_v : iter.end ≤ v.length)
    (h_end_le_16 : iter.end.val ≤ 16)
    (h_even : ∀ (j : Nat), j < v.length → (v[j]!).length % 2 = 0)
    (h_overflow : ∀ (j : Nat), j < v.length → (v[j]!).length / 2 ≤ Usize.max) :
    body i v iter out ⦃ cf =>
      match cf with
      | ControlFlow.done result =>
          result = core.result.Result.Ok { idx := i, s := EncoderState.Points out } ∧
          ¬(iter.start < iter.end)
      | ControlFlow.cont (iter1, out') =>
          iter.start < iter.end ∧
          iter1.start = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
            (∀ k, k ≠ iter.start.val → out'.val[k]! = out.val[k]!) ∧
            out'.val[iter.start.val]!.value.val.length =
              (v.val[iter.start.val]!).val.length / 2 ∧
            (∀ (k : Nat),
              k < (v.val[iter.start.val]!).val.length / 2 →
              ∃ (g : GF16),
                out'.val[iter.start.val]!.value.val[k]? = some g ∧
                g.value.val =
                  ((v.val[iter.start.val]!).val[2 * k]!).val * 256 +
                  ((v.val[iter.start.val]!).val[2 * k + 1]!).val) ⦄ := by
  unfold body
  obtain ⟨⟨opt, iter1'⟩, hnext, h_none, h_some⟩ :=
    WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_spec' iter)
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_j_lt_v : iter.start.val < v.val.length := by grind
    have h_j_lt_16 : iter.start.val < 16 := by omega
    have h_ev := h_even iter.start.val h_j_lt_v
    have h_ov := h_overflow iter.start.val h_j_lt_v
    step*
    · simp only [alloc.vec.Vec.len] at *
      grind
    · simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.len] at *
      · grind
    · simp_all [alloc.vec.Vec.with_capacity, alloc.vec.Vec.len]
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩


/-! # Spec theorem for `PolyEncoder::from_pb`: loop 1

The outer point-deserialization loop. Repeatedly invokes the loop body to deserialize each `v[j]`
into a `Point` (validating even length, then running the inner byte-pair loop) and store it in
the output array.

**Loop invariant**: `iter'.end = iter.end`, `iter'.start ≤ iter'.end`, and for all
`j < iter'.start`, `out'[j]` is the deserialized form of `v[j]` (big-endian byte-pair decoding
into GF(2¹⁶) elements).

At termination, the output array contains fully deserialized points for `v[0..iter.end]`.
Proved by lifting `body_spec` through `loop.spec_decr_nat` with measure `iter.end - iter.start`.

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem loop_spec
    (i : U32)
    (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (iter : core.ops.range.Range Usize)
    (out : Array Point 16#usize)
    (h_end_le_v : iter.end ≤ v.length)
    (h_end_le_16 : iter.end.val ≤ 16)
    (h_start_le : iter.start ≤ iter.end)
    (h_even : ∀ (j : Nat), j < v.length → (v.val[j]!).length % 2 = 0)
    (h_overflow : ∀ (j : Nat), j < v.length → (v.val[j]!).length / 2 ≤ Usize.max)
    (h_pre : ∀ (j : Nat), j < iter.start → out[j]!.value.length = (v[j]!).length / 2 ∧
          ∀ (k : Nat), k < v[j]!.length / 2 →
              out[j]!.value[k]!.value.val = (v[j]!)[2 * k]! * 256 + (v[j]!)[2 * k + 1]!) :
    from_pb_loop1 iter i v out ⦃ (result : core.result.Result PolyEncoder PolynomialError) =>
      ∃ (out' : Array Point 16#usize),
        result = core.result.Result.Ok { idx := i, s := EncoderState.Points out' } ∧
        ∀ (j : Nat), j < iter.end →
            out'[j]!.value.length = (v[j]!).length / 2 ∧
            ∀ (k : Nat), k < (v[j]!).length / 2 →
                out'[j]!.value[k]!.value.val = (v[j]!)[2 * k]! * 256 + (v[j]!)[2 * k + 1]! ⦄ := by
  unfold from_pb_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × Array Point 16#usize) => p.1.end - p.1.start)
    (inv := fun (p : core.ops.range.Range Usize × Array Point 16#usize) =>
        p.1.end = iter.end ∧
        p.1.start.val ≤ p.1.end.val ∧
        (∀ (j : Nat), j < p.1.start.val →
          ∃ (pt : encoding.polynomial.Point),
            p.2.val[j]! = pt ∧
            pt.value.val.length =
              (v.val[j]!).val.length / 2 ∧
            ∀ (k : Nat), k < (v.val[j]!).length / 2 →
                pt.value[k]!.value.val = (v[j]!)[2 * k]! * 256 + (v[j]!)[2 * k + 1]!))
  · rintro ⟨iter', out'⟩ ⟨h_end', h_start_le', h_pre'⟩
    simp only [] at h_end' h_start_le' h_pre' ⊢
    have h_end_val : iter'.end.val = iter.end.val := by rw [h_end']
    have h_body := body_spec i v iter' out' (by grind) (by omega) h_even h_overflow
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done result => grind
    | ControlFlow.cont (iter'', out'') =>
      simp only at h_cf ⊢
      obtain ⟨h_lt, h_start1, h_end1,  h_out_preserve, h_pt_len, h_pt_encode⟩ := h_cf
      constructor
      · refine ⟨by rw [h_end1]; exact h_end',
               by grind,
               fun j hj => ?_⟩
        by_cases hj_lt : j < iter'.start.val
        · obtain ⟨pt', h_eq', h_len', h_enc'⟩ := h_pre' j hj_lt
          exact ⟨pt', (h_out_preserve j (by omega)).trans h_eq', h_len', h_enc'⟩
        · grind
      · grind
  · grind

end spqr.encoding.polynomial.PolyEncoder.from_pb_loop1

namespace spqr.encoding.polynomial.PolyEncoder

/-- The two shapes `from_pb` accepts. The `polys` case also requires non-zero element
lengths, since `Poly::deserialize` rejects an empty slice whereas the points loop accepts
one. -/
def FromPbWellFormed (pb : proto.pq_ratchet.PolynomialEncoder) : Prop :=
  (pb.pts.val = [] ∧ pb.polys.length = 16 ∧
      ∀ j < 16, (pb.polys[j]!).length ≠ 0 ∧ (pb.polys[j]!).length % 2 = 0) ∨
  (pb.polys.val = [] ∧ pb.pts.length = 16 ∧
      ∀ j < 16, (pb.pts[j]!).length % 2 = 0)

instance instDecidableFromPbWellFormed (pb : proto.pq_ratchet.PolynomialEncoder) :
    Decidable (FromPbWellFormed pb) := by
  unfold FromPbWellFormed
  infer_instance

/-- Postcondition of `from_pb_spec`. Reusing `IntoPbPostCond` pins `from_pb` down as the
inverse of `into_pb` rather than by restating the byte layout. -/
def FromPbPostCond (pb : proto.pq_ratchet.PolynomialEncoder)
    (result : core.result.Result PolyEncoder PolynomialError) : Prop :=
  if FromPbWellFormed pb then
    match result with
    | core.result.Result.Ok encoder => IntoPbPostCond encoder pb
    | core.result.Result.Err _ => False
  else result = core.result.Result.Err PolynomialError.SerializationInvalid

/-- **Spec theorem for `spqr::encoding::polynomial::PolyEncoder::from_pb`**
• The call always succeeds (no panic).
• If `pb` is well-formed, then the result is `Ok` with an encoder that serializes back to
  `pb`, stated via `PolyEncoder.IntoPbPostCond`; the `| .Err _ => False` branch rules out failure.
• On any other `pb` the result is `Err PolynomialError.SerializationInvalid`, the only error
  value `from_pb` can produce.
-/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.PolynomialEncoder) :
    from_pb pb ⦃ (result : core.result.Result PolyEncoder PolynomialError) =>
      FromPbPostCond pb result ⦄ := by
  unfold FromPbPostCond
  by_cases h_wf : FromPbWellFormed pb
  · simp only [if_pos h_wf]
    obtain ⟨h1, h2, h3⟩ :
        (pb.pts.val = [] → ∀ j < pb.polys.length, (pb.polys[j]!).length ≠ 0) ∧
        (pb.pts.val = [] → ∀ j < pb.polys.length, (pb.polys[j]!).length % 2 = 0) ∧
        (pb.polys.val = [] → ∀ j < pb.pts.length, (pb.pts[j]!).length % 2 = 0) := by
      rcases h_wf with ⟨_, h_len, h_el⟩ | ⟨_, h_len, h_el⟩ <;> simp_all [alloc.vec.Vec.length]
    have h_bytes : from_pb pb ⦃ (result : core.result.Result PolyEncoder PolynomialError) =>
          (pb.pts.val = [] → pb.polys.length = 16 →
            match result with
            | core.result.Result.Ok encoder =>
                encoder.idx = pb.idx ∧
                match encoder.s with
                | EncoderState.Polys out =>
                    ∀ j < 16, (out[j]!).degree = (pb.polys[j]!).length / 2 ∧
                        ∀ k < (pb.polys[j]!).length / 2,
                          (out[j]!.coefficients[k]!).value.val =
                              256 * ((pb.polys[j]!)[2 * k]!).val + ((pb.polys[j]!)[2 * k + 1]!).val
                | _ => False
            | core.result.Result.Err _ => False) ∧
          (pb.polys.val = [] → pb.pts.length = 16 →
            match result with
            | core.result.Result.Ok encoder =>
                encoder.idx = pb.idx ∧
                match encoder.s with
                | EncoderState.Points out =>
                    ∀ j < 16, (out[j]!).value.length = (pb.pts[j]!).length / 2 ∧
                        ∀ k < (pb.pts[j]!).length / 2,
                            ((out[j]!).value[k]!).value.val =
                              256 * ((pb.pts[j]!)[2 * k]!).val +
                              ((pb.pts[j]!)[2 * k + 1]!).val
                | _ => False
            | core.result.Result.Err _ => False) ⦄ := by
      clear * - pb h1 h2 h3
      unfold from_pb
      step*
      · grind
      · grind
      · refine ⟨fun _ _ => ?_, fun h _ => ?_⟩
        · cases result with
          | Err _ => exact result_post
          | Ok enc =>
            obtain ⟨h_idx, h_enc⟩ := result_post
            refine ⟨h_idx, ?_⟩
            revert h_enc
            cases enc.s with
            | Points _ => exact id
            | Polys out =>
              intro h_enc
              exact fun j hj => h_enc ⟨j, by scalar_tac⟩ (by
                change j < ↑i1; rw [i1_post]; exact hj)
        · simp_all
      · grind
      · grind
      all_goals simp_all [List.isEmpty_iff, List.isEmpty_eq_false_iff]
    apply WP.spec_mono h_bytes
    intro result ⟨h_polys, h_pts⟩
    rcases h_wf with ⟨h_nil, h_len, h_el⟩ | ⟨h_nil, h_len, h_el⟩
    · match result, h_polys h_nil h_len with
      | .Ok ⟨_, .Polys out⟩, ⟨h_idx, h_enc⟩ => exact ⟨h_idx.symm, by grind⟩
    · match result, h_pts h_nil h_len with
      | .Ok ⟨_, .Points out⟩, ⟨h_idx, h_enc⟩ => exact ⟨h_idx.symm, by grind⟩
  · simp only [if_neg h_wf]
    have h_des : ∀ (s : Slice U8),
        Poly.deserialize s ⦃ (r : core.result.Result Poly PolynomialError) =>
          match r with
          | core.result.Result.Ok _ => s.length ≠ 0 ∧ s.length % 2 = 0
          | core.result.Result.Err e => e = PolynomialError.SerializationInvalid ⦄ := by
      clear * - pb
      intro s
      unfold Poly.deserialize
      step*
      simp [alloc.vec.Vec.with_capacity]
    have h_b0 : ∀ (i : U32) (v : alloc.vec.Vec (alloc.vec.Vec U8))
        (iter : core.ops.range.Range Usize) (out : Array Poly 16#usize),
        iter.end ≤ v.length → iter.end.val ≤ 16 → iter.start.val < iter.end.val →
        from_pb_loop0.body i v iter out ⦃ cf =>
          match cf with
          | ControlFlow.done result =>
              result = core.result.Result.Err PolynomialError.SerializationInvalid
          | ControlFlow.cont (iter1, _) =>
              iter1.start.val = iter.start.val + 1 ∧ iter1.end = iter.end ∧
              (v[iter.start.val]!).length ≠ 0 ∧ (v[iter.start.val]!).length % 2 = 0 ⦄ := by
      clear * - pb h_des
      intro i v iter out h_end_le_v h_end_le_16 h_lt
      unfold from_pb_loop0.body
      obtain ⟨⟨opt, iter1'⟩, hnext, h_none, h_some⟩ :=
        WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_spec' iter)
      rw [hnext]
      simp only [bind_tc_ok]
      obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
      rw [h_opt_eq]
      have h_idx : iter.start.val < v.length := by scalar_tac
      have h_16 : iter.start.val < 16 := by omega
      step as ⟨v1, hv1⟩
      step with h_des (alloc.vec.Vec.deref v1) as ⟨r, hr⟩
      cases r <;> step*
      simp_all [alloc.vec.Vec.deref, Slice.length, alloc.vec.Vec.length]
    have h_b1 : ∀ (i : U32) (v : alloc.vec.Vec (alloc.vec.Vec U8))
        (iter : core.ops.range.Range Usize) (out : Array Point 16#usize),
        iter.end ≤ v.length → iter.end.val ≤ 16 → iter.start.val < iter.end.val →
        from_pb_loop1.body i v iter out ⦃ cf =>
          match cf with
          | ControlFlow.done result =>
              result = core.result.Result.Err PolynomialError.SerializationInvalid
          | ControlFlow.cont (iter1, _) =>
              iter1.start.val = iter.start.val + 1 ∧ iter1.end = iter.end ∧
              (v[iter.start.val]!).length % 2 = 0 ⦄ := by
      clear * - pb
      intro i v iter out h_end_le_v h_end_le_16 h_lt
      unfold from_pb_loop1.body
      obtain ⟨⟨opt, iter1'⟩, hnext, h_none, h_some⟩ :=
        WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_spec' iter)
      rw [hnext]
      simp only [bind_tc_ok]
      obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
      rw [h_opt_eq]
      have h_idx : iter.start.val < v.length := by scalar_tac
      have h_16 : iter.start.val < 16 := by omega
      step*
      all_goals simp_all [alloc.vec.Vec.len, alloc.vec.Vec.length, alloc.vec.Vec.with_capacity]
      all_goals grind
    have h_l0 : ∀ (i : U32) (v : alloc.vec.Vec (alloc.vec.Vec U8))
        (iter : core.ops.range.Range Usize) (out : Array Poly 16#usize),
        iter.end ≤ v.length → iter.end.val ≤ 16 →
        (∃ j, iter.start.val ≤ j ∧ j < iter.end.val ∧
          ((v[j]!).length = 0 ∨ (v[j]!).length % 2 ≠ 0)) →
        from_pb_loop0 iter i v out ⦃ (result : core.result.Result PolyEncoder PolynomialError) =>
          result = core.result.Result.Err PolynomialError.SerializationInvalid ⦄ := by
      clear * - pb h_b0
      intro i v iter out h_end_le_v h_end_le_16 h_bad
      unfold from_pb_loop0
      apply loop.spec_decr_nat
        (measure := fun p => p.1.end.val - p.1.start.val)
        (inv := fun p => p.1.end = iter.end ∧
            ∃ j, p.1.start.val ≤ j ∧ j < p.1.end.val ∧
              ((v[j]!).length = 0 ∨ (v[j]!).length % 2 ≠ 0))
      · rintro ⟨iter', out'⟩ ⟨h_end', jb, hjb1, hjb2, hjb_bad⟩
        simp only at h_end' hjb1 hjb2 ⊢
        apply WP.spec_mono
          (h_b0 i v iter' out' (h_end' ▸ h_end_le_v) (h_end' ▸ h_end_le_16) (by omega))
        intro cf hcf
        match cf with
        | ControlFlow.done result => exact hcf
        | ControlFlow.cont (iter'', out'') => grind
      · exact ⟨rfl, h_bad⟩
    have h_l1 : ∀ (i : U32) (v : alloc.vec.Vec (alloc.vec.Vec U8))
        (iter : core.ops.range.Range Usize) (out : Array Point 16#usize),
        iter.end ≤ v.length → iter.end.val ≤ 16 →
        (∃ j, iter.start.val ≤ j ∧ j < iter.end.val ∧ (v[j]!).length % 2 ≠ 0) →
        from_pb_loop1 iter i v out ⦃ (result : core.result.Result PolyEncoder PolynomialError) =>
          result = core.result.Result.Err PolynomialError.SerializationInvalid ⦄ := by
      clear * - pb h_b1
      intro i v iter out h_end_le_v h_end_le_16 h_bad
      unfold from_pb_loop1
      apply loop.spec_decr_nat
        (measure := fun p => p.1.end.val - p.1.start.val)
        (inv := fun p => p.1.end = iter.end ∧
            ∃ j, p.1.start.val ≤ j ∧ j < p.1.end.val ∧ (v[j]!).length % 2 ≠ 0)
      · rintro ⟨iter', out'⟩ ⟨h_end', jb, hjb1, hjb2, hjb_bad⟩
        simp only at h_end' hjb1 hjb2 ⊢
        apply WP.spec_mono
          (h_b1 i v iter' out' (h_end' ▸ h_end_le_v) (h_end' ▸ h_end_le_16) (by omega))
        intro cf hcf
        match cf with
        | ControlFlow.done result => exact hcf
        | ControlFlow.cont (iter'', out'') => grind
      · exact ⟨rfl, h_bad⟩
    unfold from_pb
    obtain ⟨n, hn, hn_post⟩ := WP.spec_imp_exists NUM_POLYS_spec
    simp only [alloc.vec.Vec.is_empty, alloc.vec.Vec.len, hn, bind_tc_ok]
    split
    next h_pts =>
      have h_pts' : pb.pts.val = [] := by simpa [List.isEmpty_iff] using h_pts
      split
      next h_len =>
        step as ⟨p, hp⟩
        refine h_l0 _ _ _ _ (by scalar_tac) (by scalar_tac) ?_
        by_contra h_c
        push Not at h_c
        exact h_wf (Or.inl ⟨h_pts', by scalar_tac,
          fun j hj => h_c j (by simp) (by scalar_tac)⟩)
      next h_len => simp
    next h_pts =>
      split
      next h_polys =>
        have h_polys' : pb.polys.val = [] := by simpa [List.isEmpty_iff] using h_polys
        split
        next h_ne => simp
        next h_ne =>
          refine h_l1 _ _ _ _ (by scalar_tac) (by scalar_tac) ?_
          by_contra h_c
          push Not at h_c
          exact h_wf (Or.inr ⟨h_polys', by scalar_tac,
            fun j hj => h_c j (by simp) (by scalar_tac)⟩)
      next h_polys => simp

/- The rest of the file is there to establish that the refactor lost nothing: the new spec above
   generalises the old one, additionally dropping all three input hypotheses and pinning
   down the error case.
• `FromPbPostCondOld`: the exact postcondition of the old `from_pb_spec`, with the
   byte-level, GF(2¹⁶) and binary polynomial identities spelled out.
• `from_pb_new_implies_old`: a theorem that derives `FromPbPostCondOld` from the new
  `FromPbPostCond`, given the three hypotheses on `pb` that the old spec assumed.
• `from_pb_spec_old`: the exact old spec theorem, now proven as a corollary via `from_pb_spec`
   by `WP.spec_mono`. Not `@[step]` anymore, so that new proofs now consume the
   generalised `from_pb_spec`. -/

/-- The postcondition `from_pb_spec` carried before it was generalised: byte-level
serialization identities behind implications that say nothing about rejected inputs. -/
def FromPbPostCondOld (pb : proto.pq_ratchet.PolynomialEncoder)
    (result : core.result.Result PolyEncoder PolynomialError) : Prop :=
  (pb.pts.val = [] → pb.polys.val.length = 16 →
    match result with
    | core.result.Result.Ok encoder =>
        encoder.idx = pb.idx ∧
        match encoder.s with
        | EncoderState.Polys out =>
            ∀ j < 16, (out[j]!).degree = (pb.polys[j]!).length / 2 ∧
                ∀ k < (pb.polys[j]!).length / 2,
                    (out[j]!.coefficients[k]!).value.val =
                      256 * ((pb.polys[j]!)[2 * k]!).val + ((pb.polys[j]!)[2 * k + 1]!).val ∧
                    ((out[j]!.coefficients[k]!).value.val).toGF216 =
                      (256 * ((pb.polys[j]!)[2 * k]!).val +
                       ((pb.polys[j]!)[2 * k + 1]!).val).toGF216 ∧
                    natToBinaryPoly (out[j]!.coefficients[k]!).value.val =
                      natToBinaryPoly
                        (256 * ((pb.polys[j]!)[2 * k]!).val +
                         ((pb.polys[j]!)[2 * k + 1]!).val)
        | _ => False
    | core.result.Result.Err _ => False) ∧
  (pb.polys.val = [] → pb.pts.length = 16 →
    match result with
    | core.result.Result.Ok encoder =>
        encoder.idx = pb.idx ∧
        match encoder.s with
        | EncoderState.Points out =>
            ∀ j < 16, (out[j]!).value.length = (pb.pts[j]!).length / 2 ∧
            ∀ k < (pb.pts[j]!).length / 2,
                ((out[j]!).value[k]!).value.val =
                256 * ((pb.pts[j]!)[2 * k]!).val + ((pb.pts[j]!)[2 * k + 1]!).val ∧
                (((out[j]!).value[k]!).value.val).toGF216 =
                  (256 * ((pb.pts[j]!)[2 * k]!).val + ((pb.pts[j]!)[2 * k + 1]!).val).toGF216 ∧
                natToBinaryPoly ((out[j]!).value[k]!).value.val =
                natToBinaryPoly (256 * ((pb.pts[j]!)[2 * k]!).val +
                         ((pb.pts[j]!)[2 * k + 1]!).val)
        | _ => False
    | core.result.Result.Err _ => False)

theorem from_pb_new_implies_old
    (pb : proto.pq_ratchet.PolynomialEncoder)
    (h_polys_nonempty : pb.pts.val = [] → ∀ j < pb.polys.length, (pb.polys[j]!).length ≠ 0)
    (h_polys_even : pb.pts.val = [] → ∀ j < pb.polys.length, (pb.polys[j]!).length % 2 = 0)
    (h_pts_even : pb.polys.val = [] → ∀ j < pb.pts.length, (pb.pts[j]!).length % 2 = 0)
    (result : core.result.Result PolyEncoder PolynomialError)
    (h_total : FromPbPostCond pb result) :
    FromPbPostCondOld pb result := by
  unfold FromPbPostCond at h_total
  unfold FromPbPostCondOld
  refine ⟨fun h_nil h_len => ?_, fun h_nil h_len => ?_⟩
  · have h_len' : pb.polys.length = 16 := h_len
    rw [if_pos (show FromPbWellFormed pb from .inl ⟨h_nil, h_len', fun j hj =>
      ⟨h_polys_nonempty h_nil j (by omega), h_polys_even h_nil j (by omega)⟩⟩)] at h_total
    match result, h_total with
    | .Ok ⟨_, .Points _⟩, ⟨_, h_polys_nil, _⟩ => simp [h_polys_nil] at h_len
    | .Ok ⟨_, .Polys out⟩, ⟨h_idx, _, _, h_body⟩ =>
      have h_out : out.length = 16 := out.property
      refine ⟨h_idx.symm, fun j hj => ?_⟩
      obtain ⟨h_lenj, h_co⟩ := h_body j (by omega)
      refine ⟨by omega, fun k hk => ?_⟩
      obtain ⟨e1, e2, e3⟩ := h_co k (by omega)
      exact ⟨e1.symm, e2.symm, e3.symm⟩
  · rw [if_pos (show FromPbWellFormed pb from .inr ⟨h_nil, h_len, fun j hj =>
      h_pts_even h_nil j (by omega)⟩)] at h_total
    match result, h_total with
    | .Ok ⟨_, .Polys _⟩, ⟨_, h_pts_nil, _⟩ => simp [h_pts_nil] at h_len
    | .Ok ⟨_, .Points out⟩, ⟨h_idx, _, _, h_body⟩ =>
      have h_out : out.length = 16 := out.property
      refine ⟨h_idx.symm, fun j hj => ?_⟩
      obtain ⟨h_lenj, h_co⟩ := h_body j (by omega)
      refine ⟨by omega, fun k hk => ?_⟩
      obtain ⟨e1, e2, e3⟩ := h_co k (by omega)
      exact ⟨e1.symm, e2.symm, e3.symm⟩

theorem from_pb_spec_old
    (pb : proto.pq_ratchet.PolynomialEncoder)
    (h_polys_nonempty : pb.pts.val = [] → ∀ j < pb.polys.length, (pb.polys[j]!).length ≠ 0)
    (h_polys_even : pb.pts.val = [] → ∀ j < pb.polys.length, (pb.polys[j]!).length % 2 = 0)
    (h_pts_even : pb.polys.val = [] → ∀ j < pb.pts.length, (pb.pts[j]!).length % 2 = 0) :
    from_pb pb ⦃ (result : core.result.Result PolyEncoder PolynomialError) =>
      FromPbPostCondOld pb result ⦄ :=
  WP.spec_mono (from_pb_spec pb)
    (from_pb_new_implies_old pb h_polys_nonempty h_polys_even h_pts_even)

end spqr.encoding.polynomial.PolyEncoder
