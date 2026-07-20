/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-! # Spec theorem for `PolyDecoder::new_with_poly_count` closure `call_mut`

The closure `|_| SortedSet::new()` in `new_with_poly_count` ignores its index
and returns a fresh empty `SortedSet<Pt>`. It captures nothing, so the closure
state is `Unit`. The extracted `call_mut` creates a new sorted set and returns
it paired with the unchanged closure state.

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial


namespace spqr.encoding.polynomial.PolyDecoder.new_with_poly_count.closure
namespace Insts.CoreOpsFunctionFnMutTupleUsizeSortedSetPt

/-- **Spec theorem for `PolyDecoder.new_with_poly_count.closure.call_mut`**:

Succeeds whenever `SortedSet.new` succeeds and returns the closure state
unchanged: `result.2 = c`. -/
@[step]
theorem call_mut_spec
    (c : PolyDecoder.new_with_poly_count.closure)
    (tupled_args : Usize) :
    call_mut c tupled_args ⦃ (result : (sorted_vec.SortedSet Pt) ×
    PolyDecoder.new_with_poly_count.closure) =>
      result.2 = c ⦄ := by
  unfold call_mut
  simp [sorted_vec.SortedSet.new]

end Insts.CoreOpsFunctionFnMutTupleUsizeSortedSetPt
end spqr.encoding.polynomial.PolyDecoder.new_with_poly_count.closure
