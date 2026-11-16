/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong, Markus Dablander
-/
module

public import Spqr.Math.List
public import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Polynomial.Pt.Serialize
import Spqr.Specs.Aeneas.RangeIteratorNext
public import Spqr.Math.Poly.Basic.Defs
public import SrcTranslated.Funs
public import Spqr.Specs.Encoding.Polynomial.Poly.FunctionalModels
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Order.Int.ConditionallyCompleteOrder
import Spqr.Specs.Aeneas.IndexRangeFull

/-!
# Spec theorem for `Poly::serialize`: loop body 0

One step of the coefficient serialization loop: either the iterator is exhausted (output
unchanged) or the next coefficient is encoded as 2 big-endian bytes appended to the output.
Invariant: `out.len() == 2 * i`, with `out[2*j] * 256 + out[2*j+1] = v[j].value.val` for `j < i`.

**Source**: spqr/src/encoding/polynomial.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.Poly.serialize_loop

/--
**Spec for `alloc.vec.Vec.extend_from_slice` specialised to `U8`**:

Cloning `U8` is the identity, so appending `s` yields `v.val ++ s.val`. The precondition
`v.val.length + s.val.length ≤ Usize.max` discharges the overflow guard. -/
@[step]
private lemma extend_from_slice_U8_spec
    (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s
      ⦃ (r : alloc.vec.Vec U8) => r = v ++ s.val ⦄ := by
  have h_clone_x :
      ∀ x ∈ s.val, core.clone.CloneU8.clone x = ok x := by
    intros _ _; rfl
  unfold alloc.vec.Vec.extend_from_slice
  rw [dite_eq_left h]
  step*

/-- **Spec theorem for `encoding.polynomial.Poly.serialize_loop.body`**:

One step of the serialize loop. Preconditions: `iter.end.val ≤ v.len` and, whenever a
coefficient is still to come, room for two more bytes. In the **done** case `out` is unchanged
and `¬(iter.start.val < iter.end.val)`. In the **cont** case the iterator advances by one
(`iter1.start = iter.start + 1`, `iter1.end = iter.end`) and `out` gains the two big-endian bytes
of the current coefficient: `out1.val = out.val ++ [hi, lo]` with
`hi.val * 256 + lo.val = (v.val[iter.start.val]!).value.val`.

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem body_spec
    (v : alloc.vec.Vec GF16)
    (iter : core.ops.range.Range Usize)
    (out : alloc.vec.Vec U8)
    (h_end_le : iter.end ≤ v.val.length)
    (h_out_overflow : iter.start < iter.end → out.length + 2 ≤ Usize.max) :
    body v iter out ⦃ cf =>
      match cf with
      | ControlFlow.done out' =>
          out' = out ∧ ¬(iter.start < iter.end)
      | ControlFlow.cont (iter1, out1) =>
          iter.start < iter.end ∧
          iter1.start = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          ∃ (hi lo : Std.U8),
            out1.val = out.val ++ [hi, lo] ∧
            256 * hi  + lo = (v.val[iter.start.val]!).value.val ⦄ := by
  unfold body
  step with core.iter.range.IteratorRange.next_Usize_spec' iter as
    ⟨opt, iter1', h_none, h_some⟩
  by_cases h_lt : iter.start < iter.end.val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_i_lt : iter.start.val < v.val.length := by omega
    have h_room : out.length + 2 ≤ Usize.max := h_out_overflow h_lt
    step*
    obtain ⟨b0, b1, h_a_eq⟩ : ∃ b0 b1, a.val = [b0, b1] :=
      match a.val, a.property with | [b0, b1], _ => ⟨b0, b1, rfl⟩
    refine ⟨h_lt, h_start1, h_end1, b0, b1, ?_, ?_⟩
    · simp_all [Array.to_slice]
    · have e0 : (a[0]!).val = b0.val := by simp [Array.getElem!_Nat_eq, h_a_eq]
      have e1 : (a[1]!).val = b1.val := by simp [Array.getElem!_Nat_eq, h_a_eq]
      grind
  · obtain ⟨rfl, -⟩ := h_none h_lt
    exact (WP.spec_ok _).mpr ⟨rfl, h_lt⟩

end spqr.encoding.polynomial.Poly.serialize_loop

/-! # Spec theorem for `Poly::serialize`: loop 0

The full top-level `serialize_loop`, which drives the body to completion. Each coefficient's
`u16` value is encoded as two big-endian bytes. Loop invariant: `out'.len = 2 * iter'.start`,
`iter'.end` unchanged, and `hi * 256 + lo = v[j].value` for every processed index `j`. The
proof lifts `body_spec` via `loop.spec_decr_nat` with measure `iter'.end.val − iter'.start.val`.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.Poly.serialize_loop

/-- **Spec theorem for `encoding.polynomial.Poly.serialize_loop`**:

The full serialization loop driving the body to completion. Preconditions: `iter.end.val ≤ v.len`,
`out.len = 2 * iter.start`, `iter.start ≤ iter.end`, and `2 * v.len ≤ Usize.max`. Postcondition:
`result.len = 2 * iter.end.val` and for every `j < iter.end.val` the bytes satisfy
`hi * 256 + lo = (v.val[j]!).value.val`. Proved via `loop.spec_decr_nat` with measure
`iter'.end.val − iter'.start.val`. -/
@[step]
theorem loop_spec
    (v : alloc.vec.Vec GF16)
    (iter : core.ops.range.Range Usize)
    (out : alloc.vec.Vec U8)
    (h_end_le : iter.end ≤ v.val.length)
    (h_out_len : out.length = 2 * iter.start)
    (h_start_le : iter.start ≤ iter.end)
    (h_overflow : 2 * v.val.length ≤ Usize.max)
    (h_pre : ∀ (j : Nat), j < iter.start.val →
          256 * out[2 * j]! + out[2 * j + 1]! = (v[j]!).value.val) :
    serialize_loop iter v out ⦃ (result : alloc.vec.Vec Std.U8) =>
      result.length = 2 * iter.end ∧
      ∀ (j : Nat), j < iter.end →
          256 * result[2 * j]! + result[2 * j + 1]! = (v[j]!).value.val ⦄ := by
  unfold serialize_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × alloc.vec.Vec U8) => p.1.end - p.1.start)
    (inv := fun (p : core.ops.range.Range Usize × alloc.vec.Vec U8) =>
        let iter' := p.1
        let out' := p.2
        iter'.end = iter.end ∧
        iter'.start ≤ iter'.end.val ∧
        out'.val.length = 2 * iter'.start ∧
        (∀ (j : Nat), j < iter'.start →
          256 * out'[2 * j]! + out'[2 * j + 1]! = (v.val[j]!).value.val))
  · rintro ⟨iter', out'⟩ ⟨h_end', h_start_le', h_out_len', h_pre'⟩
    simp only [] at h_end' h_start_le' h_out_len' h_pre' ⊢
    have h_end_val : iter'.end = iter.end := by rw [h_end']
    have h_body := body_spec v iter' out' (by grind) (fun h_lt => by
      have h_lt' : iter'.start.val < iter'.end.val := h_lt
      have h_end_val' : iter'.end.val = iter.end.val := by rw [h_end']
      have h_end_le' : iter.end.val ≤ v.val.length := h_end_le
      have h_out_len'' : out'.val.length = 2 * iter'.start.val := h_out_len'
      have h_overflow' : 2 * v.val.length ≤ Usize.max := h_overflow
      change out'.val.length + 2 ≤ Usize.max
      omega)
    apply WP.spec_mono h_body
    rintro (⟨iter1, out1⟩ | out'') h
    · obtain ⟨h_lt, h_s1, h_e1, hi, lo, h_out1, h_hilo⟩ := h
      refine ⟨⟨h_e1.trans h_end', by grind,
        by simp only [h_out1, List.length_append, List.length_cons, List.length_nil]; omega, ?_⟩,
        by grind⟩
      intro j hj
      dsimp only at hj
      simp only [alloc.vec.Vec.getElem!_Nat_eq, h_out1]
      by_cases hj' : j < iter'.start.val
      · rw [List.getElem!_append_left _ _ _ (by omega),
          List.getElem!_append_left _ _ _ (by omega)]
        exact h_pre' j hj'
      · have hj_eq : j = iter'.start.val := by omega
        subst hj_eq
        rw [List.getElem!_append_right _ _ _ (by omega),
          List.getElem!_append_right _ _ _ (by omega), h_out_len', Nat.sub_self,
          Nat.add_sub_cancel_left]
        exact h_hilo
    · obtain ⟨rfl, h_nlt⟩ := h
      exact ⟨by grind, fun j hj => h_pre' j (by grind)⟩
  · exact ⟨rfl, h_start_le, h_out_len, h_pre⟩

end spqr.encoding.polynomial.Poly.serialize_loop

/-! # Spec theorem for `spqr::encoding::polynomial::{Poly}::serialize`

Serializes a polynomial's GF(2¹⁶) coefficients into a byte vector: allocate a vector of capacity
`2 * n`, then encode each coefficient's `u16` value as two big-endian bytes. The result has length
`2 * n` with `result[2*j] * 256 + result[2*j+1] = coefficients[j].value` for every `j`.

`serialize` is **total and never fails** — in particular it does *not* special-case the zero
polynomial. Since `Poly::zero` has an empty coefficient vector (`zero_spec`), `serialize` of the
zero polynomial is the empty byte string `[]`, which `Poly::deserialize` rejects with
`SerializationInvalid` (`deserialize_spec`). Hence `deserialize ∘ serialize` is **not** the
identity on `Poly::zero`; see `docs/defects.md`, item 16.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.Poly

/-- **Byte-level spec theorem for `encoding.polynomial.Poly.serialize`**:

Total characterisation of `Poly::serialize`, stated for **every** `Poly` (including the zero
polynomial) so that the defect-16 behaviour is pinned down rather than assumed away:

  * `result.length = 2 * self.degree` — two big-endian bytes per coefficient, no header, no
    padding. Consequently `result = [] ↔ self.coefficients = []`: the zero polynomial and *only*
    the zero polynomial serialises to the empty byte string, which `deserialize` rejects.
  * `serialized.length % 2 = 0` — the output always passes `deserialize`'s parity check; the
    emptiness check is therefore the *only* way a `serialize` output can be rejected.
  * For every `j < self.degree`:
      `256 * result[2*j]! + result[2*j+1]! = (self.coefficients[j]!).value.val`.

The precondition `2 * self.degree ≤ Usize.max` is exact: the `usize` capacity computation
`len * 2` needs it, and the final append needs nothing more. It is the size conjunct of
`FunctionalModels.WellFormed`. Proved by composing `Vec.with_capacity` with
`serialize_loop.loop_spec`. Stepping stone to `serialize_spec`, which pins the result to the
functional model. -/
theorem serialize_spec_postcond
    (self : Poly)
    (h_overflow : 2 * self.degree ≤ Usize.max) :
    serialize self ⦃ (result : alloc.vec.Vec U8) =>
      result.length = 2 * self.degree ∧
      result.length % 2 = 0 ∧
      (result.val = [] ↔ self.coefficients.val = []) ∧
      ∀ j < self.degree,
        256 * result[2 * j]! + result[2 * j +1]! = (self.coefficients[j]!).value.val ⦄ := by
  unfold serialize degree
  step*
  · simp_all [degree]; grind [alloc.vec.Vec.with_capacity]
  · simp_all [degree]; grind [alloc.vec.Vec.with_capacity]
  · rw [alloc.vec.Vec.len_val] at result_post result_post1
    refine ⟨result_post, by omega, ?_, result_post1⟩
    simp only [← List.length_eq_zero_iff]
    simp only [alloc.vec.Vec.length] at result_post
    omega

/-- **Corollary (defect 16 witness, `serialize` side)**: a polynomial with no coefficients — the
representation `Poly::zero` produces (`zero_spec`) — serialises to the empty byte string. Combined
with `deserialize_empty_is_err`, `Poly::deserialize (Poly::serialize zero)` is
`Err SerializationInvalid`, so the two functions are not inverses on the zero polynomial. -/
theorem serialize_zero_eq_nil
    (self : Poly)
    (h_zero : self.coefficients.val = []) :
    serialize self ⦃ (result : alloc.vec.Vec U8) => result.val = [] ⦄ := by
  have h_deg : self.degree = 0 := by simp [degree, h_zero]
  apply WP.spec_mono (serialize_spec_postcond self (by rw [h_deg]; scalar_tac))
  intro result h
  exact h.2.2.1.mpr h_zero

/-- **Spec theorem for `encoding.polynomial.Poly.serialize`**
• The call always succeeds (no panic) under the hypothesis `2 * self.degree ≤ Usize.max`
  of `serialize_spec_postcond`, the size conjunct of `FunctionalModels.WellFormed`.
• The extracted function agrees with its associated high-level functional model
  `FunctionalModels.serialize` (see def): the byte string `FunctionalModels.bytesOfCoeffs` of the
  coefficient list, as a vector.
-/
@[step]
theorem serialize_spec
    (self : Poly)
    (h_overflow : 2 * self.degree ≤ Usize.max) :
    serialize self ⦃ (result : alloc.vec.Vec U8) =>
      result = FunctionalModels.serialize self ⦄ := by
  apply WP.spec_mono (serialize_spec_postcond self h_overflow)
  intro result h
  obtain ⟨h_len, -, -, h_enc⟩ := h
  unfold degree at h_overflow h_len h_enc
  simp only [alloc.vec.Vec.length] at h_overflow h_len h_enc
  refine (FunctionalModels.eq_ofList_bytesOfCoeffs_iff result _ (by omega)).mpr
    ⟨h_len, fun k hk => ?_⟩
  simpa only [alloc.vec.Vec.getElem!_Nat_eq, List.Inhabited_getElem_eq_getElem! _ _ hk]
    using h_enc k hk

end spqr.encoding.polynomial.Poly
