/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import Spqr.Math.List
public import Spqr.Math.Gf16.Field
public import Spqr.Specs.Encoding.Polynomial.Pt.Deserialize
public import Spqr.Specs.Aeneas.RangeIteratorNext


/-! # Spec theorem for `Poly::deserialize`: loop body 0

One step of the coefficient deserialization `while i < serialized_len` loop. Either:

  1. **Done**: `i ≥ serialized_len`, `coefficients` returned unchanged.
  2. **Continue**: reads the two bytes `serialized[i]` and `serialized[i+1]`, decodes them
     as a big-endian `u16`, wraps as `GF16`, pushes onto `coefficients` and advances `i` by 2.

Loop invariant: `i` is even, `coefficients.len() == i / 2`, with each coefficient satisfying
  `coefficients[k].value.val = 256 * serialized[2*k].val + serialized[2*k+1].val`
for all `k < i / 2`. -/

@[expose] public section

open Aeneas Aeneas.Std spqr.encoding.gf

namespace spqr.encoding.polynomial.Poly.deserialize_loop

@[step]
private lemma GF16_new_value_spec (value : U16) :
    GF16.new value ⦃ (result : GF16) =>
      result.value = value ⦄ := by
  simp [GF16.new]

@[step]
theorem body_spec
    (serialized : Slice Std.U8)
    (serialized_len : Usize)
    (coefficients : alloc.vec.Vec GF16)
    (i : Usize)
    (h_len : serialized_len.val = serialized.length)
    (h_even : serialized.length % 2 = 0)
    (h_i_even : i.val % 2 = 0)
    (h_coeff_overflow : coefficients.length + 1 ≤ Usize.max) :
    body serialized serialized_len coefficients i ⦃ (cf : ControlFlow (alloc.vec.Vec GF16 × Usize)
    (alloc.vec.Vec GF16)) =>
      match cf with
      | ControlFlow.done coefficients' =>
          coefficients' = coefficients ∧ ¬(i.val < serialized_len.val)
      | ControlFlow.cont (coefficients1, i1) =>
          i.val < serialized_len.val ∧
          i1.val = i.val + 2 ∧
          ∃ (g : GF16),
            coefficients1 = coefficients ++ [g] ∧
            g.value = 256 * (serialized[i.val]!).val + (serialized[i.val + 1]!).val ⦄ := by
  unfold body
  split
  · have h_i1_lt : i.val + 1 < serialized.length := by scalar_tac
    have h_i_lt : i.val < serialized.length := by omega
    step*
    refine ⟨by scalar_tac, by scalar_tac, _, ‹_›, ?_⟩
    simp_all [Array.make, Nat.mul_comm, getElem!_pos]
  · simp_all

end spqr.encoding.polynomial.Poly.deserialize_loop

/-!
# Spec theorem for `Poly::deserialize`: loop 0

The full deserialization loop that drives `deserialize_loop.body` to completion. Each iteration
reads a byte pair from `serialized`, decodes it as a big-endian `u16`, wraps it as `GF16`,
and appends it to the coefficient vector.

**Loop invariant** (at byte index `i'`):
  * `i'` is even and `i' ≤ serialized_len`
  * `coefficients'.length = i' / 2`
  * For every `j < i' / 2`:
    `(coefficients'[j]!).value.val = 256 * serialized[2*j]! + serialized[2*j+1]!`

At termination, the coefficient vector contains the complete deserialization of all byte pairs.
The proof lifts the body spec via `loop.spec_decr_nat` with measure `serialized_len − i'`. -/


namespace spqr.encoding.polynomial.Poly.deserialize_loop

@[step]
theorem loop_spec
    (serialized : Slice U8)
    (serialized_len : Usize)
    (coefficients : alloc.vec.Vec GF16)
    (i : Usize)
    (h_len : serialized_len.val = serialized.length)
    (h_even : serialized.length % 2 = 0)
    (h_i_even : i.val % 2 = 0)
    (h_i_le : i.val ≤ serialized_len.val)
    (h_coeff_len : coefficients.length = i.val / 2)
    (h_pre : ∀ j < i.val / 2,
      (coefficients[j]!).value.val = 256 * serialized[2 * j]! + serialized[2 * j + 1]!) :
    deserialize_loop serialized serialized_len coefficients i ⦃ (result : alloc.vec.Vec GF16) =>
      result.length = serialized.length / 2 ∧
      ∀ j < serialized.length / 2,
        result[j]!.value.val = 256 * serialized[2 * j]! + serialized[2 * j + 1]! ⦄ := by
  unfold deserialize_loop
  apply loop.spec_decr_nat
    (measure := fun (p : alloc.vec.Vec GF16 × Usize) => serialized_len.val - p.2.val)
    (inv := fun (p : alloc.vec.Vec GF16 × Usize) =>
        p.2.val % 2 = 0 ∧
        p.2.val ≤ serialized_len.val ∧
        p.1.length = p.2.val / 2 ∧
        (∀ j < p.2.val / 2,
          p.1[j]!.value.val = 256 * serialized[2 * j]! + serialized[2 * j + 1]!))
  · rintro ⟨coefficients', i'⟩ ⟨h_i_even', h_i_le', h_coeff_len', h_pre'⟩
    have h_body := body_spec serialized serialized_len coefficients' i' h_len h_even h_i_even'
      (by scalar_tac)
    apply WP.spec_mono h_body
    simp only at h_i_even' h_i_le' h_coeff_len' h_pre'
    rintro (⟨coefficients1, i1⟩ | coefficients'') hcf
    · obtain ⟨h_lt, h_i1, g, h_c1, h_g⟩ := hcf
      simp only
      have h_c1_len : coefficients1.length = coefficients'.length + 1 := by
        simp [alloc.vec.Vec.length, h_c1]
      refine ⟨⟨by omega, by omega, by omega, ?_⟩, by omega⟩
      intro j hj
      simp only [alloc.vec.Vec.getElem!_Nat_eq, alloc.vec.Vec.length] at h_pre' h_coeff_len' ⊢
      rw [h_c1]
      by_cases hjl : j < i'.val / 2
      · rw [List.getElem!_append_left _ _ _ (by omega)]
        exact h_pre' j hjl
      · have h2j : 2 * j = i'.val := by omega
        rw [List.getElem!_append_right _ _ _ (by omega), h2j,
          show j - (↑coefficients' : List GF16).length = 0 by omega]
        simpa using h_g
    · obtain ⟨rfl, h_ge⟩ := hcf
      have h_eq : i'.val = serialized.length := by omega
      refine ⟨by omega, fun j hj => h_pre' j (by omega)⟩
  · grind

end spqr.encoding.polynomial.Poly.deserialize_loop

/-! # Spec theorem for `spqr::encoding::polynomial::{Poly}::deserialize`

Deserializes a byte slice into a polynomial over GF(2¹⁶) by decoding consecutive byte pairs
as big-endian `u16` values wrapped as `GF16` elements.

Three stages:
  1. **Validation**: rejects empty or odd-length input.
  2. **Allocation**: pre-allocates a coefficient vector of capacity `serialized.len() / 2`.
  3. **Deserialization loop**: decodes each byte pair and appends the `GF16` coefficient.

This is intended to be the inverse of `Poly::serialize`, but it is **not** on the zero
polynomial: `Poly::zero` has no coefficients, so `serialize` yields `[]`, which `deserialize`
rejects with `SerializationInvalid`. -/


namespace spqr.encoding.polynomial.Poly

/-- **Spec theorem for `encoding.polynomial.Poly.deserialize`**:

Total characterisation of `Poly::deserialize` over GF(2¹⁶), stated **without** any assumption
on the shape of the input so that the error behaviour is pinned down rather than assumed away:

  * **Err branch** — the result is `Err SerializationInvalid` **iff**
    `serialized.length = 0 ∨ serialized.length % 2 = 1`. In particular the empty slice — which is
    exactly `Poly::serialize` of the zero polynomial (`serialize_spec`, `zero_spec`) — is rejected,
    so `deserialize ∘ serialize` is not the identity on `Poly::zero`. This is the Rust defect
    recorded; the `is_empty()` check is the culprit, the loop
    itself handles length 0 correctly.
  * **Ok branch** — for non-empty, even-length input:
      - `poly.degree = serialized.length / 2`
      - `∀ j < serialized.length / 2`,
        `poly.coefficients[j]!.value.val = 256 * serialized[2*j]! + serialized[2*j+1]!`

There is no precondition: the `while i < serialized_len` loop advances `i` by 2 from an even
start, so `i + 2 ≤ serialized_len` never overflows. -/
@[step]
theorem deserialize_spec
    (serialized : Slice U8) :
    deserialize serialized ⦃ (result : core.result.Result Poly PolynomialError) =>
      match result with
      | core.result.Result.Ok poly =>
          serialized.length ≠ 0 ∧
          serialized.length % 2 = 0 ∧
          poly.degree = serialized.length / 2 ∧
          ∀ j < serialized.length / 2,
            poly.coefficients[j]!.value.val = 256 * serialized[2 * j]! + serialized[2 * j + 1]!
      | core.result.Result.Err e =>
          e = PolynomialError.SerializationInvalid ∧
          (serialized.length = 0 ∨ serialized.length % 2 = 1) ⦄ := by
  unfold Poly.deserialize degree
  step*
  simp [alloc.vec.Vec.with_capacity]

/-- **Corollary (defect 16 witness)**: the byte string `Poly::serialize` produces for the zero
polynomial — the empty slice — is rejected by `Poly::deserialize`. Hence `deserialize` is not a
left inverse of `serialize` on `Poly::zero`. -/
theorem deserialize_empty_is_err
    (serialized : Slice U8)
    (h_empty : serialized.length = 0) :
    deserialize serialized ⦃ (result : core.result.Result Poly PolynomialError) =>
      result = core.result.Result.Err PolynomialError.SerializationInvalid ⦄ := by
  apply WP.spec_mono (deserialize_spec serialized)
  rintro (poly | e) h
  · exact absurd h_empty h.1
  · simp [h.1]

end spqr.encoding.polynomial.Poly
