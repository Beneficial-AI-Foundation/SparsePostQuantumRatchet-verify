/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
module

public import Aeneas

/-! # A total list-to-`Vec` conversion

`alloc.vec.Vec.from` needs a proof that its list has at most `Usize.max` elements. The functional
models of `spqr::encoding::polynomial::Poly::{serialize, deserialize}` and
`spqr::encoding::polynomial::PolyEncoder::{into_pb, from_pb}` wrap the byte strings
`Poly.FunctionalModels.bytesOfCoeffs` and the coefficient lists
`Poly.FunctionalModels.coeffsOfBytes` into vectors. A `bytesOfCoeffs` list fits only when the
coefficient list has at most `Usize.max / 2` elements, a bound a total model cannot demand up
front. A `coeffsOfBytes` list always fits, since its input is a slice or a vector, but
`coeffsOfBytes` is typed on a bare `List U8` so that `deserialize` (slice input) and `from_pb`
(vector input) can share it. `Vec.ofList` serves both uses: it keeps the list whenever the list
fits and truncates it to the first `Usize.max` elements otherwise. `ofList_val` recovers the list
once the length bound is available, and `ofList_val_self` recovers a vector from its own list. -/

@[expose] public section

open Aeneas Aeneas.Std

/-- `Vec.from` without the length proof: the vector whose list is `l` truncated to its first
`Usize.max` elements, which is all of `l` whenever `l.length ≤ Usize.max`. -/
def Aeneas.Std.alloc.vec.Vec.ofList {α : Type} (l : List α) : alloc.vec.Vec α :=
  alloc.vec.Vec.from (l.take Usize.max) (by simp)

/-- The list underlying `Vec.ofList l` is `l` itself whenever `l.length ≤ Usize.max`. -/
@[simp] theorem Aeneas.Std.alloc.vec.Vec.ofList_val {α : Type} (l : List α)
    (h : l.length ≤ Usize.max) : (alloc.vec.Vec.ofList l).val = l := by
  simp [alloc.vec.Vec.ofList, List.take_of_length_le h]

/-- `Vec.ofList` is a left inverse of `Vec.val`: a vector is recovered from its own list. -/
@[simp] theorem Aeneas.Std.alloc.vec.Vec.val_ofList {α : Type}
    (v : alloc.vec.Vec α) : alloc.vec.Vec.ofList v.val = v :=
  alloc.vec.Vec.ext _ _ (alloc.vec.Vec.ofList_val v.val v.property)
