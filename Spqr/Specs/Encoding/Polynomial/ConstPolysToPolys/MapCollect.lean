/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-! # Spec theorem for `core::iter::adapters::map::{Iterator for Map<I, F>}::collect`

`Map<I, F>` lazily applies `F` to each element of iterator `I`. `collect` drives iteration to
completion, assembling results into a collection `B1` via `FromIterator`.

It works in two stages:
  1. **Map-iterator construction** — `mapIteratorTransformer` wraps `I` so that `next` applies
     `FnMut.call_mut` with closure `map.f` to each yielded item.
  2. **Collection** — the transformed iterator is passed to `FromIterator.from_iter` to produce
     the final `B1`.

**Source**: core/src/iter/adapters/map.rs (lines 99:0-101:27) -/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator

/-- **Spec theorem for `collect`** (definitional unfolding):

Shows that `collect` on `Map<I, F>` equals calling `FromIterator.from_iter` with a blanket
`IntoIterator` wrapping the `mapIteratorTransformer`-constructed iterator:

    `collect iterInst fnMutInst fromIterInst m
       = fromIterInst.from_iter
           (IntoIterator.Blanket (mapIteratorTransformer m iterInst fnMutInst))
           m.iter`

Downstream specialised `collect_spec` theorems (e.g. for `const_polys_to_polys`) build on this
by instantiating types and unfolding `from_iter` to reason about the resulting loop. -/
@[simp, step_simps]
theorem collect_spec
    {B I F B1 Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator I Clause0_Item)
    (fnMutInst : core.ops.function.FnMut F Clause0_Item B)
    (fromIterInst : core.iter.traits.collect.FromIterator B1 B)
    (m : core.iter.adapters.map.Map I F) :
    core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect
      iterInst fnMutInst fromIterInst m =
      fromIterInst.from_iter
        (core.iter.traits.collect.IntoIterator.Blanket
          (core.iter.adapters.map.mapIteratorTransformer m iterInst fnMutInst))
        m.iter := by
  unfold core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect
    core.iter.traits.iterator.Iterator.collect.default
  rfl

end Aeneas.Std.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
