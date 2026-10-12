/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong, Markus Dablander
-/
module

public import SrcTranslated.Funs
public import Spqr.Auxiliary.Aeneas.Vec
public import Spqr.Specs.Encoding.Polynomial.NUM_POLYS
public import Spqr.Specs.Encoding.Polynomial.Poly.Zero
public import Spqr.Specs.Encoding.Polynomial.Poly.Deserialize
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.Defs
public import Spqr.Specs.Aeneas.GF16New

/-! # Spec theorem for `PolyEncoder::from_pb`: loop body 0

One step of the outer polynomial-deserialization loop
`for (i, poly) in pb.polys.iter().enumerate() { out[i] = Poly::deserialize(poly)?; }`.
Advances the enumerated slice iterator over `v = pb.polys` and either:
1. **Done (Ok)**: iterator exhausted → returns `Ok(PolyEncoder { idx: i, s: Polys(out) })`.
2. **Done (Err)**: `Poly::deserialize(v[j])` fails (`v[j]` empty or of odd length) → returns
   `Err(SerializationInvalid)`.
3. **Continue**: deserializes `v[j]` into a `Poly` via `Poly::deserialize` and updates `out[j]`.

Each coefficient satisfies the big-endian invariant:
`value = serialized[2*k] * 256 + serialized[2*k+1]`.

**Source**: spqr/src/encoding/polynomial.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf spqr.math.gf

namespace spqr.encoding.polynomial.PolyEncoder.from_pb_loop0

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.from_pb_loop0.body`**:

One step of the outer deserialization loop over `iter = v.iter().enumerate()` (the slice of the
enumerated iterator has the contents of `v`, and its count agrees with its cursor `j`). Either
terminates — with `Ok(PolyEncoder { idx := i, s := Polys out })` once the iterator is exhausted,
or with `Err(SerializationInvalid)` if `v[j]` is empty or of odd length — or deserializes `v[j]`
into a `Poly` and updates `out[j]`.

• **cont**: the cursor advances by one; `out'[j]` has degree `(v[j]!).length / 2` and each
  coefficient `k` satisfies `value = 256 * v[j][2*k] + v[j][2*k+1]`. -/
@[step]
theorem body_spec
    (i : U32) (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (alloc.vec.Vec U8)))
    (out : Array Poly 16#usize)
    (h_slice : iter.iter.slice.val = v.val)
    (h_count : iter.count.val = iter.iter.i)
    (h_le_16 : v.length ≤ 16) :
    body i iter out ⦃ cf =>
      match cf with
      | ControlFlow.done result =>
          (¬(iter.iter.i < v.length) ∧
            result = .Ok { idx := i, s := EncoderState.Polys out }) ∨
          (iter.iter.i < v.length ∧
            result = .Err PolynomialError.SerializationInvalid ∧
            ((v[iter.iter.i]!).length = 0 ∨ (v[iter.iter.i]!).length % 2 = 1))
      | ControlFlow.cont (iter1, out') =>
          iter.iter.i < v.length ∧
          iter1.iter.slice = iter.iter.slice ∧
          iter1.iter.i = iter.iter.i + 1 ∧
          iter1.count.val = iter1.iter.i ∧
          (v[iter.iter.i]!).length ≠ 0 ∧ (v[iter.iter.i]!).length % 2 = 0 ∧
          (∀ (k : Nat), k ≠ iter.iter.i → out'[k]! = out[k]!) ∧
          (out'[iter.iter.i]!).degree = (v[iter.iter.i]!).length / 2 ∧
          (∀ k < (v[iter.iter.i]!).length / 2,
              ((out'[iter.iter.i]!).coefficients[k]!).value.val =
                256 * (v[iter.iter.i]!)[2 * k]! + (v[iter.iter.i]!)[2 * k + 1]!) ⦄ := by
  unfold body core.iter.adapters.enumerate.IteratorEnumerate.next
  simp only [core.slice.iter.IteratorSliceIter.next]
  have h_sl : iter.iter.slice.len.val = v.val.length := by simp [h_slice]
  split
  · have h_i : iter.iter.i < v.val.length := by omega
    obtain ⟨c', hc_eq, hc_val⟩ : ∃ c', iter.count + 1#usize = ok c' ∧
        c'.val = iter.count.val + 1 := by
      obtain ⟨c', hc', hval⟩ :=
        WP.spec_imp_exists (Usize.add_spec (x := iter.count) (y := 1#usize) (by scalar_tac))
      exact ⟨c', hc', by scalar_tac⟩
    simp only [bind_tc_ok, hc_eq, bind_ok]
    step as ⟨r, hr⟩
    have h_el : iter.iter.slice[iter.iter.i] = v[iter.iter.i]! := by
      rw [alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos v.val _ h_i]
      simp only [← h_slice]
      rfl
    have h_dv : (alloc.vec.Vec.deref iter.iter.slice[iter.iter.i]).val =
        (v[iter.iter.i]!).val := by
      simp [alloc.vec.Vec.deref, h_el]
    rcases r with poly | e
    · step*
      simp only [Slice.length, Slice.getElem!_Nat_eq, h_dv] at hr
      obtain ⟨h_ne, h_ev, h_deg, h_coef⟩ := hr
      obtain rfl : val = poly := by simp_all
      have h_cnt : iter.count.val = iter.iter.i := h_count
      have h_len16 : out.val.length = 16 := by simp
      have h_a : a.val = out.val.set iter.iter.i val := by
        rw [‹a = _›, ‹index_mut_back = _›]
        simp [h_cnt]
      have h_slot : a[iter.iter.i]! = val := by
        rw [Array.getElem!_Nat_eq, h_a, List.getElem!_eq_getElem?_getD,
          List.getElem?_set_self (by simp only [alloc.vec.Vec.length] at h_le_16; omega)]
        rfl
      simp only [alloc.vec.Vec.length] at h_ne h_ev h_deg h_coef ⊢
      refine ⟨h_i, by omega, h_ne, h_ev, ?_, by rw [h_slot]; exact h_deg, ?_⟩
      · intro k hk
        rw [Array.getElem!_Nat_eq, Array.getElem!_Nat_eq, h_a, List.getElem!_eq_getElem?_getD,
          List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hk)]
      · intro k hk
        rw [h_slot, h_coef k hk]
        simp only [alloc.vec.Vec.getElem!_Nat_eq]
    · step*
  · step*

/-! # Spec theorem for `PolyEncoder::from_pb`: loop 0

The outer polynomial-deserialization loop. Repeatedly invokes the loop body to deserialize each
`v[j]` into a `Poly` and store it in the output array.

**Loop invariant**: the enumerated iterator walks over `v` with count equal to its cursor `j'`,
and for all `j < j'`, `out'[j]` is the deserialized form of `v[j]` (big-endian byte-pair
decoding).

At termination, either the output array contains fully deserialized polynomials for all of `v`
(and every remaining `v[j]` was non-empty and of even length), or some remaining `v[j]` was
empty or of odd length and the result is `Err(SerializationInvalid)`.

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem loop_spec
    (i : U32)
    (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (alloc.vec.Vec U8)))
    (out : Array Poly 16#usize)
    (h_slice : iter.iter.slice.val = v.val)
    (h_count : iter.count.val = iter.iter.i)
    (h_le_16 : v.length ≤ 16)
    (h_pre : ∀ j < iter.iter.i, (out[j]!).degree = (v[j]!).length / 2 ∧
      ∀ k < (v[j]!).length / 2,
          ((out[j]!).coefficients[k]!).value.val = 256 * (v[j]!)[2 * k]! + (v[j]!)[2 * k + 1]!) :
    from_pb_loop0 iter i out ⦃ (result : core.result.Result PolyEncoder PolynomialError) =>
      match result with
      | core.result.Result.Ok encoder =>
          encoder.idx = i ∧
          (∀ j, iter.iter.i ≤ j → j < v.length →
            (v[j]!).length ≠ 0 ∧ (v[j]!).length % 2 = 0) ∧
          match encoder.s with
          | EncoderState.Polys out' =>
              ∀ j < v.length, (out'[j]!).degree = (v[j]!).length / 2 ∧
              ∀ k < (v[j]!).length / 2,
              ((out'[j]!).coefficients[k]!).value.val = 256 * (v[j]!)[2 * k]! + (v[j]!)[2 * k + 1]!
          | _ => False
      | core.result.Result.Err e =>
          e = PolynomialError.SerializationInvalid ∧
          ∃ j, iter.iter.i ≤ j ∧ j < v.length ∧
            ((v[j]!).length = 0 ∨ (v[j]!).length % 2 = 1) ⦄ := by
  unfold from_pb_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter (alloc.vec.Vec U8)) × Array Poly 16#usize) =>
      v.length - p.1.iter.i)
    (inv := fun (p : core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter (alloc.vec.Vec U8)) × Array Poly 16#usize) =>
        p.1.iter.slice = iter.iter.slice ∧
        p.1.count.val = p.1.iter.i ∧
        iter.iter.i ≤ p.1.iter.i ∧
        (∀ j, iter.iter.i ≤ j → j < p.1.iter.i →
          (v[j]!).length ≠ 0 ∧ (v[j]!).length % 2 = 0) ∧
        (∀ j < p.1.iter.i, (p.2[j]!).degree = (v[j]!).length / 2 ∧
          ∀ k < (v[j]!).length / 2,
            ((p.2[j]!).coefficients[k]!).value.val = 256 * (v[j]!)[2 * k]! + (v[j]!)[2 * k + 1]!))
  · rintro ⟨iter', out'⟩ ⟨h_sl', h_count', h_le', h_ok', h_pre'⟩
    simp only at h_sl' h_count' h_le' h_ok' h_pre' ⊢
    have h_body := body_spec i v iter' out' (by rw [h_sl']; exact h_slice) h_count' h_le_16
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done result =>
      simp only at h_cf ⊢
      rcases h_cf with ⟨h_ge, rfl⟩ | ⟨h_lt, rfl, h_bad⟩
      · exact ⟨rfl, fun j hj1 hj2 => h_ok' j hj1 (by omega),
          fun j hj => h_pre' j (by omega)⟩
      · exact ⟨rfl, iter'.iter.i, h_le', h_lt, h_bad⟩
    | ControlFlow.cont (iter'', out'') =>
      simp only at h_cf ⊢
      obtain ⟨h_lt, h_sl1, h_i1, h_count1, h_ne, h_ev, h_other, h_deg, h_coef⟩ := h_cf
      refine ⟨⟨by rw [h_sl1, h_sl'], h_count1, by omega, ?_, fun j hj => ?_⟩, by omega⟩
      · intro j hj1 hj2
        by_cases hj : j < iter'.iter.i
        · exact h_ok' j hj1 hj
        · have : j = iter'.iter.i := by omega
          subst this
          exact ⟨h_ne, h_ev⟩
      · by_cases hj_lt : j < iter'.iter.i
        · rw [h_other j (by omega)]
          exact h_pre' j hj_lt
        · have hj_eq : j = iter'.iter.i := by omega
          subst hj_eq
          exact ⟨h_deg, h_coef⟩
  · exact ⟨rfl, h_count, le_refl _, fun j hj1 hj2 => absurd hj2 (by simp only; omega), h_pre⟩

end spqr.encoding.polynomial.PolyEncoder.from_pb_loop0

/-! # Spec theorem for `PolyEncoder::from_pb`: loop body 2

One step of the inner byte-deserialization loop (Points branch)
`while j < pts_len { v.push(GF16::new(u16::from_be_bytes([pts[j], pts[j + 1]]))); j += 2; }`.
Either:
1. **Done**: `j ≥ pts_len` → loop terminates.
2. **Continue**: reads `pts[j]` and `pts[j+1]`, converts to `u16` via big-endian decoding,
   wraps as `GF16::new`, pushes onto `v`, and advances `j` by 2.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyEncoder.from_pb_loop1_loop0

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.from_pb_loop1_loop0.body`**:

One step of the inner byte-deserialization loop. Given serialized byte vector `pts` of even
length `pts_len`, an even cursor `j`, and output vector `v` of `GF16` values:

• **done**: `¬ (j < pts_len)`, output unchanged.
• **cont**: `j` advances by two; `v` is extended by one `GF16` element whose value is
  `pts[j] * 256 + pts[j+1]` (big-endian reconstruction). -/
@[step]
theorem body_spec
    (pts : alloc.vec.Vec U8)
    (pts_len : Usize)
    (v : alloc.vec.Vec GF16)
    (j : Usize)
    (h_len : pts_len.val = pts.length)
    (h_even : pts.length % 2 = 0)
    (h_j_even : j.val % 2 = 0)
    (h_overflow : v.length + 1 ≤ Usize.max) :
    body pts pts_len v j ⦃ cf =>
      match cf with
      | ControlFlow.done v_final =>
          ¬(j.val < pts_len.val) ∧
          v_final = v
      | ControlFlow.cont (v1, j1) =>
          j.val < pts_len.val ∧
          j1.val = j.val + 2 ∧
          ∃ (g : GF16),
            v1.val = v.val ++ [g] ∧
            g.value.val = 256 * pts[j.val]! + pts[j.val + 1]! ⦄ := by
  unfold body
  split
  · have h_j1_lt : j.val + 1 < pts.length := by scalar_tac
    have h_j_lt : j.val < pts.length := by omega
    step*
    refine ⟨by scalar_tac, by scalar_tac, _, ‹_›, ?_⟩
    simp_all [Array.make, Nat.mul_comm, getElem!_pos]
  · simp_all

/-! # Spec theorem for `PolyEncoder::from_pb`: loop 2

The inner byte-deserialization loop (Points branch). Repeatedly invokes the loop body to
reconstruct GF(2¹⁶) elements from byte pairs in `pts`.

**Loop invariant** (at byte index `j'`): `j'` is even, `j' ≤ pts_len`,
`v'.length = j' / 2`, and every element `k < j' / 2` satisfies
`value = 256 * pts[2*k] + pts[2*k+1]`.

At termination, the output vector contains all deserialized GF(2¹⁶) elements.
Proved by lifting `body_spec` through `loop.spec_decr_nat` with measure `pts_len - j'`.

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem loop_spec
    (pts : alloc.vec.Vec U8)
    (v : alloc.vec.Vec GF16)
    (pts_len : Usize)
    (j : Usize)
    (h_len : pts_len.val = pts.length)
    (h_even : pts.length % 2 = 0)
    (h_j_even : j.val % 2 = 0)
    (h_j_le : j.val ≤ pts_len.val)
    (h_v_len : v.length = j.val / 2)
    (h_pre : ∀ k < j.val / 2,
      (v[k]!).value.val = 256 * pts[2 * k]! + pts[2 * k + 1]!) :
    from_pb_loop1_loop0 pts v pts_len j ⦃ (v_result : alloc.vec.Vec GF16) =>
      v_result.length = pts.length / 2 ∧
      ∀ k < pts.length / 2,
        (v_result[k]!).value.val = 256 * pts[2 * k]! + pts[2 * k + 1]! ⦄ := by
  unfold from_pb_loop1_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : alloc.vec.Vec GF16 × Usize) => pts_len.val - p.2.val)
    (inv := fun (p : alloc.vec.Vec GF16 × Usize) =>
        p.2.val % 2 = 0 ∧
        p.2.val ≤ pts_len.val ∧
        p.1.length = p.2.val / 2 ∧
        (∀ k < p.2.val / 2,
          (p.1[k]!).value.val = 256 * pts[2 * k]! + pts[2 * k + 1]!))
  · rintro ⟨v', j'⟩ ⟨h_j_even', h_j_le', h_v_len', h_pre'⟩
    have h_body := body_spec pts pts_len v' j' h_len h_even h_j_even' (by scalar_tac)
    apply WP.spec_mono h_body
    simp only at h_j_even' h_j_le' h_v_len' h_pre'
    rintro (⟨v1, j1⟩ | v'') hcf
    · obtain ⟨h_lt, h_j1, g, h_v1, h_g⟩ := hcf
      simp only
      have h_v1_len : v1.length = v'.length + 1 := by
        simp [alloc.vec.Vec.length, h_v1]
      refine ⟨⟨by omega, by omega, by omega, ?_⟩, by omega⟩
      intro k hk
      simp only [alloc.vec.Vec.getElem!_Nat_eq, alloc.vec.Vec.length] at h_pre' h_v_len' ⊢
      rw [h_v1]
      by_cases hkl : k < j'.val / 2
      · rw [List.getElem!_append_left _ _ _ (by omega)]
        exact h_pre' k hkl
      · have h2k : 2 * k = j'.val := by omega
        rw [List.getElem!_append_right _ _ _ (by omega), h2k,
          show k - (↑v' : List GF16).length = 0 by omega]
        simpa using h_g
    · obtain ⟨h_ge, rfl⟩ := hcf
      have h_eq : j'.val = pts.length := by omega
      refine ⟨by omega, fun k hk => h_pre' k (by omega)⟩
  · exact ⟨h_j_even, h_j_le, h_v_len, h_pre⟩

end spqr.encoding.polynomial.PolyEncoder.from_pb_loop1_loop0

/-! # Spec theorem for `PolyEncoder::from_pb`: loop body 1

One step of the outer point-deserialization loop (Points branch). Advances the range iterator
and either:
1. **Done (Ok)**: iterator exhausted → returns `Ok(PolyEncoder { idx: i, s: Points(out) })`.
2. **Done (Err)**: byte vector has odd length → returns `Err(SerializationInvalid)`.
3. **Continue**: runs the inner loop to reconstruct GF(2¹⁶) elements from byte pairs, constructs
   a `Point`, and stores it in `out[j]`.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyEncoder.from_pb_loop1

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.from_pb_loop1.body`**:

One step of the outer point-deserialization loop. Retrieves the next index `j` and either
terminates (wrapping output as `Ok(PolyEncoder { idx := i, s := Points out })` when the
iterator is exhausted, or `Err(SerializationInvalid)` when `v[j]` has odd length) or
deserializes `v[j]` into a `Point` via the inner byte-pair loop and updates `out[j]`.

• **cont**: iterator advances by one; `out'[j]` has `pt.value.length = v[j].length / 2` and each
  element `k` satisfies `value = v[j][2*k] * 256 + v[j][2*k+1]`. -/
@[step]
theorem body_spec
    (i : U32)
    (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (iter : core.ops.range.Range Usize)
    (out : Array Point 16#usize)
    (h_end_le_v : iter.end ≤ v.length)
    (h_end_le_16 : iter.end.val ≤ 16) :
    body i v iter out ⦃ cf =>
      match cf with
      | ControlFlow.done result =>
          (¬(iter.start < iter.end) ∧
            result = core.result.Result.Ok { idx := i, s := EncoderState.Points out }) ∨
          (iter.start < iter.end ∧
            result = core.result.Result.Err PolynomialError.SerializationInvalid ∧
            (v[iter.start.val]!).length % 2 ≠ 0)
      | ControlFlow.cont (iter1, out') =>
          iter.start < iter.end ∧
          (v[iter.start.val]!).length % 2 = 0 ∧
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
  step with core.iter.range.IteratorRange.next_Usize_spec' iter as
    ⟨opt, iter1', h_none, h_some⟩
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    simp only [h_opt_eq]
    have h_j_lt_v : iter.start.val < v.val.length := by scalar_tac
    have h_j_lt_16 : iter.start.val < 16 := by omega
    step as ⟨pts, h_pts⟩
    have h_pts' : v[iter.start.val]! = pts := by
      rw [h_pts, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos v.val _ h_j_lt_v]
    step as ⟨i3, h_i3⟩
    split
    · simp only [WP.spec_ok]
      refine Or.inr ⟨h_lt, trivial, ?_⟩
      rw [h_pts']
      simp only [bne_iff_ne, ne_eq, UScalar.neq_to_neq_val, alloc.vec.Vec.len] at *
      scalar_tac
    · have h_mod : pts.val.length % 2 = 0 := by
        simp only [bne_iff_ne, ne_eq, UScalar.neq_to_neq_val, not_not, alloc.vec.Vec.len] at *
        scalar_tac
      step with from_pb_loop1_loop0.loop_spec pts
        (alloc.vec.Vec.with_capacity GF16 (alloc.vec.Vec.len pts)) (alloc.vec.Vec.len pts)
        0#usize
        (by simp [alloc.vec.Vec.len]) h_mod (by simp) (by simp)
        (by simp [alloc.vec.Vec.with_capacity])
        (by simp) as ⟨v2, h_v2_len, h_v2⟩
      step*
      have h_vv : v.val[iter.start.val]! = pts := by
        rw [← alloc.vec.Vec.getElem!_Nat_eq]; exact h_pts'
      have h_len16 : out.val.length = 16 := by simp
      have h_a : a.val = out.val.set iter.start.val { value := v2 } := by
        rw [‹a = _›, ‹index_mut_back = _›]
        simp
      have h_slot : a.val[iter.start.val]! = { value := v2 } := by
        rw [h_a, List.getElem!_eq_getElem?_getD, List.getElem?_set_self (by omega)]
        rfl
      simp only [alloc.vec.Vec.length] at h_v2_len
      refine ⟨h_lt, by rw [h_pts']; exact h_mod, h_start1, h_end1, ?_, ?_, ?_⟩
      · intro k hk
        rw [h_a, List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
          List.getElem?_set_ne (Ne.symm hk)]
      · rw [h_slot, h_vv]
        exact h_v2_len
      · intro k hk
        rw [h_vv] at hk ⊢
        have hk' : k < v2.val.length := by omega
        refine ⟨v2.val[k], ?_, ?_⟩
        · rw [h_slot]
          exact List.getElem?_eq_getElem hk'
        · have := h_v2 k hk
          simp only [alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos v2.val k hk'] at this
          rw [this]
          ring
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    simp [h_opt_eq, h_lt]


/-! # Spec theorem for `PolyEncoder::from_pb`: loop 1

The outer point-deserialization loop. Repeatedly invokes the loop body to deserialize each `v[j]`
into a `Point` (validating even length, then running the inner byte-pair loop) and store it in
the output array.

**Loop invariant**: `iter'.end = iter.end`, `iter.start ≤ iter'.start ≤ iter'.end`, every
`v[j]` with `iter.start ≤ j < iter'.start` has even length, and for all `j < iter'.start`,
`out'[j]` is the deserialized form of `v[j]` (big-endian byte-pair decoding into GF(2¹⁶)
elements).

At termination, either the output array contains fully deserialized points for `v[0..iter.end]`,
or some `v[j]` with `iter.start ≤ j < iter.end` has odd length and the result is
`Err(SerializationInvalid)`.
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
    (h_pre : ∀ (j : Nat), j < iter.start → out[j]!.value.length = (v[j]!).length / 2 ∧
          ∀ (k : Nat), k < v[j]!.length / 2 →
              out[j]!.value[k]!.value.val = (v[j]!)[2 * k]! * 256 + (v[j]!)[2 * k + 1]!) :
    from_pb_loop1 iter i v out ⦃ (result : core.result.Result PolyEncoder PolynomialError) =>
      match result with
      | core.result.Result.Ok encoder =>
          encoder.idx = i ∧
          (∀ (j : Nat), iter.start ≤ j → j < iter.end → (v[j]!).length % 2 = 0) ∧
          match encoder.s with
          | EncoderState.Points out' =>
              ∀ (j : Nat), j < iter.end →
                out'[j]!.value.length = (v[j]!).length / 2 ∧
                ∀ (k : Nat), k < (v[j]!).length / 2 →
                    out'[j]!.value[k]!.value.val = (v[j]!)[2 * k]! * 256 + (v[j]!)[2 * k + 1]!
          | _ => False
      | core.result.Result.Err e =>
          e = PolynomialError.SerializationInvalid ∧
          ∃ (j : Nat), iter.start ≤ j ∧ j < iter.end ∧ (v[j]!).length % 2 ≠ 0 ⦄ := by
  unfold from_pb_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × Array Point 16#usize) => p.1.end - p.1.start)
    (inv := fun (p : core.ops.range.Range Usize × Array Point 16#usize) =>
        p.1.end = iter.end ∧
        iter.start.val ≤ p.1.start.val ∧
        p.1.start.val ≤ p.1.end.val ∧
        (∀ (j : Nat), iter.start.val ≤ j → j < p.1.start.val → (v[j]!).length % 2 = 0) ∧
        (∀ (j : Nat), j < p.1.start.val → p.2[j]!.value.length = (v[j]!).length / 2 ∧
          ∀ (k : Nat), k < (v[j]!).length / 2 →
            p.2[j]!.value[k]!.value.val = (v[j]!)[2 * k]! * 256 + (v[j]!)[2 * k + 1]!))
  · rintro ⟨iter', out'⟩ ⟨h_end', h_orig_le, h_start_le', h_mod', h_pre'⟩
    simp only at h_end' h_orig_le h_start_le' h_mod' h_pre' ⊢
    have h_end_val : iter'.end.val = iter.end.val := by rw [h_end']
    have h_body := body_spec i v iter' out' (by rw [h_end']; exact h_end_le_v) (by omega)
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done result =>
      simp only at h_cf ⊢
      rcases h_cf with ⟨h_ge, rfl⟩ | ⟨h_lt, rfl, h_bad⟩
      · have h_ge' : iter'.end.val ≤ iter'.start.val := by
          have : ¬ iter'.start.val < iter'.end.val := h_ge
          omega
        exact ⟨rfl, fun j hj1 hj2 => h_mod' j hj1 (by omega),
          fun j hj => h_pre' j (by omega)⟩
      · have h_lt' : iter'.start.val < iter'.end.val := h_lt
        exact ⟨rfl, iter'.start.val, h_orig_le, by omega, h_bad⟩
    | ControlFlow.cont (iter'', out'') =>
      simp only at h_cf ⊢
      obtain ⟨h_lt, h_mod_s, h_start1, h_end1, h_other, h_len_s, h_enc_s⟩ := h_cf
      have h_lt' : iter'.start.val < iter'.end.val := h_lt
      have h_end1_val : iter''.end.val = iter'.end.val := by rw [h_end1]
      refine ⟨⟨by rw [h_end1]; exact h_end', by omega, by omega, ?_, fun j hj => ?_⟩,
              by omega⟩
      · intro j hj1 hj2
        by_cases hj : j < iter'.start.val
        · exact h_mod' j hj1 hj
        · have : j = iter'.start.val := by omega
          subst this
          exact h_mod_s
      · by_cases hj_lt : j < iter'.start.val
        · rw [Array.getElem!_Nat_eq, h_other j (by omega), ← Array.getElem!_Nat_eq]
          exact h_pre' j hj_lt
        · have hj_eq : j = iter'.start.val := by omega
          subst hj_eq
          rw [Array.getElem!_Nat_eq]
          simp only [alloc.vec.Vec.getElem!_Nat_eq, alloc.vec.Vec.length] at h_len_s h_enc_s ⊢
          refine ⟨h_len_s, fun k hk => ?_⟩
          obtain ⟨g, hg, hgv⟩ := h_enc_s k hk
          rw [List.getElem!_eq_getElem?_getD, hg]
          exact hgv
  · exact ⟨rfl, le_refl _, h_start_le, fun j hj1 hj2 => absurd hj2 (by simp only; omega),
      fun j hj => h_pre j hj⟩

end spqr.encoding.polynomial.PolyEncoder.from_pb_loop1

namespace spqr.encoding.polynomial.PolyEncoder

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
  unfold FromPbPostCond from_pb
  simp only [alloc.vec.Vec.is_empty, alloc.vec.Vec.len, bind_ok]
  split
  next h_pts =>
    have h_pts' : pb.pts.val = [] := by simpa [List.isEmpty_iff] using h_pts
    step with NUM_POLYS_spec as ⟨n, hn_post⟩
    split
    next h_len =>
      have h_len' : pb.polys.length = 16 := by scalar_tac
      obtain ⟨p0, hp0, -⟩ := WP.spec_imp_exists (Poly.zero_spec 1#usize)
      step as ⟨out, h_out⟩
      case l => exact List.replicate 16 p0
      case hl =>
        apply core.array.from_fn_loop_const
        · intro g i
          simp [from_pb.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizePoly.call_mut, hp0]
        · scalar_tac
      case hlen => simp
      simp only [core.slice.Slice.iter, bind_ok]
      step as ⟨iter, h_iter, h_cnt⟩
      step with from_pb_loop0.loop_spec pb.idx pb.polys iter out
        (by rw [h_iter]; simp [alloc.vec.Vec.deref]) (by rw [h_cnt, h_iter]; rfl)
        (by omega) (fun j hj => absurd hj (by rw [h_iter]; simp)) as ⟨r, h_r⟩
      rw [h_iter] at h_r
      simp only [zero_le, true_imp_iff] at h_r
      rcases r with ⟨idx, st⟩ | e
      · obtain ⟨h_idx, h_ok, h_st⟩ := h_r
        have h_wf : FromPbWellFormed pb :=
          Or.inl ⟨h_pts', h_len', fun j hj => h_ok j (by omega)⟩
        rw [if_pos h_wf]
        cases st with
        | Points _ => exact h_st.elim
        | Polys out' =>
          have h_enc : ∀ j < 16, (out'[j]!).degree = (pb.polys[j]!).length / 2 ∧
              ∀ k < (pb.polys[j]!).length / 2,
                (out'[j]!.coefficients[k]!).value.val =
                  256 * ((pb.polys[j]!)[2 * k]!).val + ((pb.polys[j]!)[2 * k + 1]!).val :=
            fun j hj => h_st j (by omega)
          have h_even : ∀ j < 16, (pb.polys[j]!).length % 2 = 0 :=
            fun j hj => (h_ok j (by omega)).2
          clear h_st h_ok h_wf h_out h_len hp0 h_pts h_iter h_cnt
          exact ⟨h_idx.symm, by grind⟩
      · obtain ⟨rfl, j, hj, hbad⟩ := h_r
        rw [if_neg]
        rintro (⟨-, -, h_el⟩ | ⟨h_nil, -, -⟩)
        · have := h_el j (by omega)
          omega
        · simp [alloc.vec.Vec.length, h_nil] at h_len'
    next h_len =>
      have h_nwf : ¬ FromPbWellFormed pb := by
        rintro (⟨-, h16, -⟩ | ⟨-, h16, -⟩)
        · exact h_len (by scalar_tac)
        · simp [alloc.vec.Vec.length, h_pts'] at h16
      simp only [WP.spec_ok, if_neg h_nwf]
  next h_pts =>
    have h_pts' : pb.pts.val ≠ [] := by simpa [List.isEmpty_iff] using h_pts
    split
    next h_polys =>
      have h_polys' : pb.polys.val = [] := by simpa [List.isEmpty_iff] using h_polys
      step with NUM_POLYS_spec as ⟨n, hn_post⟩
      split
      next h_ne =>
        have h_nwf : ¬ FromPbWellFormed pb := by
          rintro (⟨h_nil, -, -⟩ | ⟨-, h16, -⟩)
          · exact h_pts' h_nil
          · simp only [bne_iff_ne, ne_eq] at h_ne
            exact h_ne (by scalar_tac)
        simp only [WP.spec_ok, if_neg h_nwf]
      next h_ne =>
        have h_len' : pb.pts.length = 16 := by
          simp only [bne_iff_ne, ne_eq, not_not] at h_ne
          scalar_tac
        step as ⟨out, h_out⟩
        case l => exact List.replicate 16 ⟨alloc.vec.Vec.new GF16⟩
        case hl =>
          apply core.array.from_fn_loop_const
          · intro g i
            simp [from_pb.closure.Insts.CoreOpsFunctionFnMutTupleUsizePoint.call_mut]
          · scalar_tac
        case hlen => simp
        step with from_pb_loop1.loop_spec pb.idx pb.pts { start := 0#usize, «end» := n } out
          (by simp only; scalar_tac) (by simp only; omega) (by simp only; scalar_tac)
          (fun j hj => absurd hj (by simp)) as ⟨r, h_r⟩
        simp only [zero_le, true_imp_iff, hn_post] at h_r
        rcases r with ⟨idx, st⟩ | e
        · obtain ⟨h_idx, h_ok, h_st⟩ := h_r
          have h_wf : FromPbWellFormed pb :=
            Or.inr ⟨h_polys', h_len', fun j hj => h_ok j (by omega)⟩
          rw [if_pos h_wf]
          cases st with
          | Polys _ => exact h_st.elim
          | Points out' =>
            have h_enc : ∀ j < 16, (out'[j]!).value.length = (pb.pts[j]!).length / 2 ∧
                ∀ k < (pb.pts[j]!).length / 2,
                  ((out'[j]!).value[k]!).value.val =
                    256 * ((pb.pts[j]!)[2 * k]!).val + ((pb.pts[j]!)[2 * k + 1]!).val := by
              intro j hj
              obtain ⟨h1, h2⟩ := h_st j hj
              exact ⟨h1, fun k hk => by rw [h2 k hk]; ring⟩
            have h_even : ∀ j < 16, (pb.pts[j]!).length % 2 = 0 := h_ok
            clear h_st h_ok h_wf h_out h_ne h_pts h_polys
            exact ⟨h_idx.symm, by grind⟩
        · obtain ⟨rfl, j, -, hj, hbad⟩ := h_r
          have h_nwf : ¬ FromPbWellFormed pb := by
            rintro (⟨h_nil, -, -⟩ | ⟨-, -, h_el⟩)
            · exact h_pts' h_nil
            · exact hbad (h_el j hj)
          simp only [if_neg h_nwf]
    next h_polys =>
      have h_polys' : pb.polys.val ≠ [] := by simpa [List.isEmpty_iff] using h_polys
      have h_nwf : ¬ FromPbWellFormed pb := by
        rintro (⟨h_nil, -, -⟩ | ⟨h_nil, -, -⟩)
        · exact h_pts' h_nil
        · exact h_polys' h_nil
      simp only [WP.spec_ok, if_neg h_nwf]

/-- The old spec theorem for `from_pb`, kept to establish that the refactor lost nothing: it is
now a corollary of the generalised `from_pb_spec` via `WP.spec_mono. Not `@[step]` anymore, so that
new proofs consume the now more general, high-level `from_pb_spec` that includes the error case.
-/
theorem from_pb_spec_old_partial
    (pb : proto.pq_ratchet.PolynomialEncoder)
    (h_polys_nonempty : pb.pts.val = [] → ∀ j < pb.polys.length, (pb.polys[j]!).length ≠ 0)
    (h_polys_even : pb.pts.val = [] → ∀ j < pb.polys.length, (pb.polys[j]!).length % 2 = 0)
    (h_pts_even : pb.polys.val = [] → ∀ j < pb.pts.length, (pb.pts[j]!).length % 2 = 0) :
    from_pb pb ⦃ (result : core.result.Result PolyEncoder PolynomialError) =>
      FromPbPostCondOldPartial pb result ⦄ :=
  WP.spec_mono (from_pb_spec pb)
    (from_pb_new_implies_old_partial pb h_polys_nonempty h_polys_even h_pts_even)

end spqr.encoding.polynomial.PolyEncoder
