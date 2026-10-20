/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.NewWithPolyCount
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.PointsValid

/-! # Spec theorem for `spqr::encoding::polynomial::{impl Decoder for PolyDecoder}::new`

Delegates to `new_with_poly_count(len_bytes, 16)`. Returns `Ok` with
`pts_needed = len_bytes / 2` when `len_bytes` is even, or `Err MessageLengthEven` otherwise.

**Source**: spqr/src/encoding/polynomial.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.new`**
(nat-level):

Thin wrapper around `new_with_poly_count` with poly count fixed to 16.
When `len_bytes % 2 = 0`, returns `Ok { pts_needed := len_bytes / 2, pts := [∅; 16],
is_complete := false }`; otherwise returns `Err MessageLengthEven`. -/
@[step]
theorem new_spec (len_bytes : Std.Usize) :
    new len_bytes ⦃ (result : core.result.Result
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
  unfold new
  step*
  assumption

/-! ## `new` establishes the `PointsValid` invariant -/

/-- A point array all of whose slots are `default` (empty) satisfies `PointsValid`. -/
theorem PointsValid_replicate_default (pts : Array (sorted_vec.SortedSet Pt) 16#usize)
    (h : pts.val = List.replicate 16 default) : PointsValid pts := by
  apply PointsValid_of_forall_nil
  intro s hs
  rw [h, List.mem_replicate] at hs
  rw [hs.2]
  rfl

/-- **`new_with_poly_count` establishes `PointsValid`**: on success the fresh decoder's 16
slots are all empty, hence trivially sorted. -/
theorem new_with_poly_count_spec_valid (len_bytes _polys : Std.Usize) :
    new_with_poly_count len_bytes _polys ⦃ (result : core.result.Result
        encoding.polynomial.PolyDecoder encoding.EncodingError) =>
      match result with
      | core.result.Result.Ok pd => PointsValid pd.pts
      | core.result.Result.Err _ => True ⦄ := by
  apply WP.spec_mono (new_with_poly_count_spec len_bytes _polys)
  intro r hr
  split at hr
  · rcases r with pd | e
    · exact PointsValid_replicate_default pd.pts hr.2.1
    · exact trivial
  · rw [hr]; exact trivial

/-- **`new` establishes `PointsValid`**: on success every slot of the fresh decoder is
empty, hence `SlotSorted`. -/
theorem new_spec_valid (len_bytes : Std.Usize) :
    new len_bytes ⦃ (result : core.result.Result
        encoding.polynomial.PolyDecoder encoding.EncodingError) =>
      match result with
      | core.result.Result.Ok pd => PointsValid pd.pts
      | core.result.Result.Err _ => True ⦄ := by
  unfold new
  exact new_with_poly_count_spec_valid len_bytes 16#usize

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder
