/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.NewWithPolyCount

/-!
# Spec theorem for `spqr::encoding::polynomial::{impl Decoder for PolyDecoder}::new`

Delegates to `new_with_poly_count(len_bytes, 16)`. Returns `Ok` with
`pts_needed = len_bytes / 2` when `len_bytes` is even, or `Err MessageLengthEven` otherwise.

**Source**: spqr/src/encoding/polynomial.rs (lines 874:4-876:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.new`**
(nat-level):

Thin wrapper around `new_with_poly_count` with poly count fixed to 16.
When `len_bytes % 2 = 0`, returns `Ok { pts_needed := len_bytes / 2, pts := [∅; 16],
is_complete := false }`; otherwise returns `Err MessageLengthEven`.
Follows directly from `new_with_poly_count_spec`.

**Source**: spqr/src/encoding/polynomial.rs -/
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

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder
