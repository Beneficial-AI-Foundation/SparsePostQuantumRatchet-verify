/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-! # Spec theorem for `mapIteratorTransformer.next`

`Map<I, F>` lazily applies `F` to each element of iterator `I`. The `mapIteratorTransformer`
calls `I.next`, then applies `FnMut.call_mut` with `map.f` on each yielded item.

**Source**: core/src/iter/adapters/map.rs -/

open Aeneas

namespace Aeneas.Std.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator

/-- **Spec theorem for `mapIteratorTransformer.next`** (definitional unfolding):

Composes `iterInst.next` with `FnMut.call_mut`: yields `none` when exhausted, or
`some (f val)` otherwise. -/
@[simp, step_simps]
theorem mapIteratorTransformer_next_spec
    {B I F Clause0_Item : Type}
    (m : core.iter.adapters.map.Map I F)
    (iterInst : core.iter.traits.iterator.Iterator I Clause0_Item)
    (fnMutInst : core.ops.function.FnMut F Clause0_Item B)
    (iter : I) :
    (core.iter.adapters.map.mapIteratorTransformer m iterInst fnMutInst).next iter = (do
      let (opt, iter') ← iterInst.next iter
      match opt with
      | none => .ok (none, iter')
      | some val => do
        let (postFnVal, _) ← fnMutInst.call_mut m.f val
        .ok (some postFnVal, iter')) := by
  unfold core.iter.adapters.map.mapIteratorTransformer
    core.iter.traits.iterator.Iterator.fromNext
  rfl

end Aeneas.Std.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
