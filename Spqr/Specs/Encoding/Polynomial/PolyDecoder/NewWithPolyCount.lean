/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.CallOnce
import Spqr.Specs.Encoding.EncodingError.From
/-! # Spec theorem for `spqr::encoding::polynomial::{PolyDecoder}::new_with_poly_count`

Builds a fresh `PolyDecoder` from `len_bytes` and an ignored `_polys` parameter.

1. **Input validation** — requires `len_bytes % 2 == 0`, else returns
   `Err(PolynomialError::MessageLengthEven)`.

2. **Decoder construction** — returns `Ok(PolyDecoder { pts_needed := len_bytes / 2,
   pts := [SortedSet::new(); 16], is_complete := false })`.

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial

@[nolint defsWithUnderscore]
instance instInhabitedSortedSetPt : Inhabited (sorted_vec.SortedSet Pt) :=
  ⟨alloc.vec.Vec.new Pt⟩

namespace spqr.encoding.polynomial.PolyDecoder

/-- **`_polys` is unused**: `new_with_poly_count` yields the same result for any `_polys`. -/
theorem new_with_poly_count_polys_irrelevant (len_bytes polys polys' : Std.Usize) :
    new_with_poly_count len_bytes polys = new_with_poly_count len_bytes polys' := by
  unfold new_with_poly_count
  rfl

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.new_with_poly_count`** (nat-level):

• `Err(EncodingError.PolynomialError MessageLengthEven)` when `len_bytes.val % 2 ≠ 0`.
• `Ok(PolyDecoder { pts_needed.val = len_bytes.val / 2,
    pts.val = List.replicate 16 default, is_complete = false })` otherwise. -/
@[step]
theorem new_with_poly_count_spec (len_bytes _polys : Std.Usize) :
    new_with_poly_count len_bytes _polys ⦃ (result : core.result.Result
        encoding.polynomial.PolyDecoder encoding.EncodingError) =>
      if len_bytes.val % 2 = 0 then
        match result with
        | core.result.Result.Ok pd =>
            pd.pts_needed = ⟨len_bytes.val / 2, by
                have : len_bytes.val / 2 ≤ len_bytes.val := Nat.div_le_self _ _
                exact Nat.lt_of_le_of_lt this len_bytes.hBounds⟩ ∧
            pd.pts.val = List.replicate 16 default ∧
            pd.is_complete = false
        | core.result.Result.Err _ => False
      else
        result = core.result.Result.Err
          (encoding.EncodingError.PolynomialError
            encoding.polynomial.PolynomialError.MessageLengthEven) ⦄ := by
  unfold new_with_poly_count
  step*
  case l => exact List.replicate 16 default
  case hl =>
    apply core.array.from_fn_loop_replicate_default
    · intro i
      open PolyDecoder.new_with_poly_count.closure.Insts in
      simp [CoreOpsFunctionFnMutTupleUsizeSortedSetPt.call_mut,
        sorted_vec.SortedSet.new]
      rfl
    · scalar_tac
  case hlen => simp
  · split
    · exfalso; simp_all [bne_iff_ne, UScalar.neq_to_neq_val, UScalar.ofNatCore_val_eq]
    · subst ee_post; rfl
  · split
    · exact ⟨(by apply UScalar.val_eq_imp; exact i1_post), a_post⟩
    · exfalso; simp_all [bne_iff_ne, UScalar.ofNatCore_val_eq]

end spqr.encoding.polynomial.PolyDecoder
