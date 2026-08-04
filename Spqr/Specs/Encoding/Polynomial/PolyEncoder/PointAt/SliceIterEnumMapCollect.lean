/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `collect` on the enumerate–map pipeline in `PolyEncoder::point_at`

Corresponds to the Rust pipeline `pts[i].value.iter().enumerate().map(…).collect()`
in `PolyEncoder::point_at` (src/encoding/polynomial.rs, lines 641:25-644:21).

`collect` drives the `Map (Enumerate (Iter GF16))` iterator to completion,
building a `Vec<Pt>`. The adapter preserves the enumerate iterator and closure
state; all computation is deferred to the consumer.

**Postcondition**: `result.iter = m.iter` ∧ `result.f = m.f`
-/

open Aeneas Aeneas.Std Result core.iter.adapters.enumerate spqr.encoding.polynomial

namespace Aeneas.Std.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator

/--
**Spec theorem for `Enumerate.Insts.
CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.map`**:

Wraps an `Enumerate (Iter GF16)` iterator `e` and closure state `f` into a
`Map` adapter, always succeeding with `ok ⟨e, f⟩`.

**Postcondition**: `result.iter = e` ∧ `result.f = f`
-/
@[step]
theorem enumerate_map_spec
    (e : Enumerate (core.slice.iter.Iter spqr.encoding.gf.GF16))
    (f : PolyEncoder.point_at.closure_1) :
    Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.map
      (core.iter.traits.iterator.IteratorSliceIter spqr.encoding.gf.GF16)
      PolyEncoder.point_at.closure_1.Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt
      e f ⦃ (result : core.iter.adapters.map.Map
        (Enumerate
          (core.slice.iter.Iter spqr.encoding.gf.GF16)) PolyEncoder.point_at.closure_1) =>
      result.iter = e ∧ result.f = f ⦄ := by
  unfold Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.map
  step*

end Aeneas.Std.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
