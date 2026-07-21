/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.CallMut

/-! # Spec theorem for `PolyDecoder::new_with_poly_count` closure `call_once`

The closure `|_| SortedSet::new()` in `new_with_poly_count` ignores its index
and returns a fresh empty `SortedSet<Pt>`. It captures nothing, so the closure
state is `Unit`. The extracted `call_once` delegates to `call_mut` and returns
just the resulting sorted set (without the closure state).

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial

namespace spqr.encoding.polynomial.PolyDecoder.new_with_poly_count.closure
namespace Insts.CoreOpsFunctionFnOnceTupleUsizeSortedSetPt

/-- **Spec theorem for `PolyDecoder.new_with_poly_count.closure.call_once`**:

Always succeeds. Returns a fresh empty `SortedSet Pt`:
`result = alloc.vec.Vec.new Pt`. -/
@[step]
theorem call_once_spec
    (c : PolyDecoder.new_with_poly_count.closure)
    (i : Usize) :
    call_once c i ⦃ (result : sorted_vec.SortedSet Pt) =>
      result = alloc.vec.Vec.new Pt ⦄ := by
  unfold call_once
  step*

end Insts.CoreOpsFunctionFnOnceTupleUsizeSortedSetPt
end spqr.encoding.polynomial.PolyDecoder.new_with_poly_count.closure
