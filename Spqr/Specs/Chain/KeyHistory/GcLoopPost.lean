/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-! # Postcondition predicate for `gc_loop_spec`

Defines `GcLoopPost`, the postcondition of the garbage-collection loop over
`KeyHistory.data`. Given the original data `self`, a `trim_horizon`, and the
scan start index `i1`, the predicate asserts all ten properties on the
returned `result`:

1. 36-alignment of result length
2. `Usize.max` bound
3. Monotonic shrinkage (`result.length ≤ self.data.length`)
4. Prefix preservation (bytes before `i1` unchanged)
5. Scan-index bound (`i1 ≤ result.length`)
6. Liveness of all records at positions `≥ i1`
7. Provenance (every result record traces to a source record)
8. Completeness (every unexpired source record is retained)
9. Injective forward map (no duplication)
10. Injective reverse map (distinct unexpired sources map to distinct results)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.KeyHistory

/-- A natural number is 36-aligned (i.e. a record boundary). -/
abbrev RecordAligned (n : Nat) : Prop := n % 36 = 0

/-- A valid record index: within bounds and 36-aligned. -/
abbrev ValidRecord (v : alloc.vec.Vec U8) (m : Nat) : Prop :=
  m < v.length ∧ RecordAligned m

/-- Extract the 36-byte record at offset `m` from a vector's underlying list. -/
abbrev recordAt (v : alloc.vec.Vec U8) (m : Nat) : List U8 :=
  v.val.slice m (m + 36)

/-- Extract the 4-byte timestamp prefix at offset `m`. -/
abbrev timestampAt (v : alloc.vec.Vec U8) (m : Nat) : List U8 :=
  v.val.slice m (m + 4)

/-- The record at offset `n` in `v` is expired w.r.t. `trim_horizon`:
    `trim_horizon > timestamp` in lexicographic order. -/
abbrev IsExpired (trim_horizon : Slice U8) (v : alloc.vec.Vec U8) (n : Nat) : Prop :=
  Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val (timestampAt v n) = ok .gt

/-- Two records (at offsets `m` and `n` in possibly different vectors) are identical. -/
abbrev RecordsEq (v1 : alloc.vec.Vec U8) (m : Nat) (v2 : alloc.vec.Vec U8) (n : Nat) : Prop :=
  recordAt v1 m = recordAt v2 n

/-- Postcondition predicate for the GC loop. -/
def GcLoopPost
    (self : chain.KeyHistory)
    (trim_horizon : Slice U8) (i1 : Usize)
    (result : alloc.vec.Vec U8) : Prop :=
  -- (1) alignment
  RecordAligned result.length ∧
  -- (2) Usize.max bound
  result.length ≤ Usize.max ∧
  -- (3) shrinkage
  result.length ≤ self.data.length ∧
  -- (4) prefix preservation
  (∀ j, j < i1.val → result.val[j]! = self.data.val[j]!) ∧
  -- (5) scan-index bound
  i1.val ≤ result.length ∧
  -- (6) liveness
  (∀ m, i1.val ≤ m ∧ ValidRecord result m →
    ¬IsExpired trim_horizon result m) ∧
  -- (7) provenance
  (∀ m, ValidRecord result m →
    ∃ n, ValidRecord self.data n ∧ RecordsEq result m self.data n) ∧
  -- (8) completeness
  (∀ n, ValidRecord self.data n → ¬IsExpired trim_horizon self.data n →
    ∃ m, ValidRecord result m ∧ RecordsEq result m self.data n) ∧
  -- (9) injective forward map
  (∃ f : Nat → Nat,
    (∀ m, ValidRecord result m →
      ValidRecord self.data (f m) ∧ RecordsEq result m self.data (f m)) ∧
    (∀ m₁ m₂, ValidRecord result m₁ → ValidRecord result m₂ →
      f m₁ = f m₂ → m₁ = m₂)) ∧
  -- (10) injective reverse map
  (∃ g : Nat → Nat,
    (∀ n, ValidRecord self.data n → ¬IsExpired trim_horizon self.data n →
      ValidRecord result (g n) ∧ RecordsEq result (g n) self.data n) ∧
    (∀ n₁ n₂, ValidRecord self.data n₁ → ValidRecord self.data n₂ →
      ¬IsExpired trim_horizon self.data n₁ → ¬IsExpired trim_horizon self.data n₂ →
      g n₁ = g n₂ → n₁ = n₂))

end spqr.chain.KeyHistory
