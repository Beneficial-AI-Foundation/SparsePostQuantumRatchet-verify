/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: The Beneficial AI Foundation
-/
import SrcTranslated.Funs
import Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys.MapCollect

/-! # The single assumed bridge for `.map(...).collect()`

Aeneas mis-translates the `Iterator` impl for `Map<I, F>`
([aeneas#1043](https://github.com/AeneasVerif/aeneas/issues/1043)): it emits `map :=` and
`collect :=` fields that do not exist in `core.iter.traits.iterator.Iterator`, and omits
required ones. `aeneas-config.yml` works around this by deleting the bogus fields and
replacing the body of `next` with `sorry`, which lands at `SrcTranslated/Funs.lean`:

```
impl_def core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator ... := {
  next := sorry -- See https://github.com/AeneasVerif/aeneas/issues/1043
  ...
}
```

Every generated `.map(...).collect()` call site therefore collects through an instance whose
`next` is `sorryAx`. The intended semantics is supplied by hand in
`SrcTranslated/FunsExternal.lean` via `mapIteratorTransformer`. `collect_default_bridge`
below identifies the two.

**This lemma is an assumption, not an unfinished proof.** Its left-hand side mentions
`sorryAx`, which is opaque, so the statement is neither provable nor refutable — it is
independent, and assuming it is consistent. What it buys is that the trust surface for
*every* `.map(...).collect()` in the project is this one named statement, rather than one
ad-hoc lemma per call site.

It can only be discharged by making the model complete: either upstream fixes aeneas#1043,
or the tweak is changed to emit a faithful `next`. See
https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/409.
-/

open Aeneas Aeneas.Std Result

namespace Spqr.Aeneas

/-- Collecting through the generated `Map` iterator instance agrees with collecting through
the hand-written `mapIteratorTransformer` semantics.

Keep `_hF`. No proof step uses it, because there is no proof, but it is still part of the
statement. Deleting it would not simplify anything; it would strengthen the claim to cover
closures with mutable state, and that stronger claim is false. `mapIteratorTransformer`
freezes `map.f` and throws away the closure state `call_mut` returns, while a faithful
`Map::next` threads it. Since `sorryAx` on the left proves either version, nothing would
flag the change. Both call sites have `F = Unit`.

Blocked on https://github.com/AeneasVerif/aeneas/issues/1043. -/
theorem collect_default_bridge
    {B I F B1 Clause0_Item : Type}
    (_hF : Subsingleton F)
    (iterInst : core.iter.traits.iterator.Iterator I Clause0_Item)
    (fnMutInst : core.ops.function.FnMut F Clause0_Item B)
    (fromIterInst : core.iter.traits.collect.FromIterator B1 B)
    (m : core.iter.adapters.map.Map I F) :
    core.iter.traits.iterator.Iterator.collect.default
        (spqr.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
          iterInst fnMutInst)
        fromIterInst m =
      fromIterInst.from_iter
        (core.iter.traits.collect.IntoIterator.Blanket
          (core.iter.adapters.map.mapIteratorTransformer m iterInst fnMutInst))
        m.iter := by
  sorry -- Blocked on https://github.com/AeneasVerif/aeneas/issues/1043

end Spqr.Aeneas
