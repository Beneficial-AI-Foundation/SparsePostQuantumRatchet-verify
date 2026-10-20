module
public import Aeneas
public import SrcTranslated.Types
public import Spqr.Auxiliary.Aeneas.SpecImpExists
-- Remove when https://github.com/AeneasVerif/aeneas/issues/1415 lands
import all Aeneas.Std.String
public import Spqr.Crypto.Fips203.Refinement.KeyPairBytes
public import Spqr.Crypto.Fips203.Refinement.EncapsBytes
public import Spqr.Crypto.Fips203.Refinement.DecapsBytes
import Spqr.Crypto.Fips203.Refinement.KeyPairBytes
import Spqr.Crypto.Fips203.Refinement.EncapsBytes
import Spqr.Crypto.Fips203.Refinement.DecapsBytes

set_option linter.style.headerAlt false
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.whitespace false

@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000
open spqr
open Spqr.Mlkem

/-- [core::iter::traits::iterator::Iterator::map]:
    Source: '/rustc/library/core/src/iter/traits/iterator.rs', lines 831:4-834:34
    Name pattern: [core::iter::traits::iterator::Iterator::map]
    Visibility: public

    Concrete model of Rust's `Iterator::map`: the adapter is lazy, so `map`
    merely packages the underlying iterator together with the closure as a
    `Map { iter: self, f }` value (computation happens on demand in `next`).
    The outer `Result` is always `ok` (the call never panics). -/
@[rust_fun "core::iter::traits::iterator::Iterator::map"]
def core.iter.traits.iterator.Iterator.map.default
  {Self : Type} {B : Type} {F : Type} {Clause0_Item : Type} (IteratorInst :
  core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutFTupleClause0_ItemBInst : core.ops.function.FnMut F
  Clause0_Item B) :
  Self → F → Result (core.iter.adapters.map.Map Self F) :=
  fun self f => ok { iter := self, f := f }

/-- **Spec theorem for `Iterator::map`**: the call always succeeds and returns the
`Map` adapter that stores the underlying iterator `self` and the closure `fn`
unchanged (mapping is performed lazily by the adapter's `next`). -/
@[step]
theorem core.iter.traits.iterator.Iterator.map.default_spec
    {Self : Type} {B : Type} {F : Type} {Clause0_Item : Type}
    (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
    (opsfunctionFnMutFTupleClause0_ItemBInst :
      core.ops.function.FnMut F Clause0_Item B)
    (self : Self) (fn : F) :
    core.iter.traits.iterator.Iterator.map.default IteratorInst
      opsfunctionFnMutFTupleClause0_ItemBInst self fn
      ⦃ (m : core.iter.adapters.map.Map Self F) =>
      m.iter = self ∧ m.f = fn ⦄ := by
  simp [core.iter.traits.iterator.Iterator.map.default, WP.spec_ok]

/-- Implementation helper for `Slice.Insts.CoreCmpPartialEqArray.eq`
(`[core::array::equality::{core::cmp::PartialEq<[@T], [@U; @N]>}::eq]`,
Source: '/rustc/library/core/src/array/equality.rs', lines 48:4-48:40).

Element-wise equality of two lists, delegating per-element to the `PartialEq`
instance and short-circuiting on the first inequality; lists of different lengths
are unequal. -/
def Slice.partialEqAux {T U : Type} (cmpPartialEqInst : core.cmp.PartialEq T U) :
    List T → List U → Result Bool
  | [], [] => ok true
  | a :: xs, b :: ys => do
    let e ← cmpPartialEqInst.eq a b
    if e then Slice.partialEqAux cmpPartialEqInst xs ys else ok false
  | _, _ => ok false

/-- [core::array::equality::{core::cmp::PartialEq<[U; N]> for [T]}::eq]:
    Source: '/rustc/library/core/src/array/equality.rs', lines 48:4-48:40
    Name pattern: [core::array::equality::{core::cmp::PartialEq<[@T], [@U; @N]>}::eq] -/
@[rust_fun "core::array::equality::{core::cmp::PartialEq<[@T], [@U; @N]>}::eq"]
def Slice.Insts.CoreCmpPartialEqArray.eq
  {T : Type} {U : Type} {N : Std.Usize} (cmpPartialEqInst : core.cmp.PartialEq
  T U) :
  Slice T → Array U N → Result Bool :=
  fun s arr => Slice.partialEqAux cmpPartialEqInst s.val arr.val

/-- **Spec theorem for `PartialEq<[U; N]>::eq` on `[T]`**: element-wise comparison of
the slice against the array. The per-element behaviour is definitional in the
`PartialEq` instance, so this exposes the comparison as the list helper
`Slice.partialEqAux`. -/
@[simp]
theorem Slice.Insts.CoreCmpPartialEqArray.eq_eq
    {T U : Type} {N : Std.Usize} (cmpPartialEqInst : core.cmp.PartialEq T U)
    (s : Slice T) (arr : Array U N) :
    Slice.Insts.CoreCmpPartialEqArray.eq cmpPartialEqInst s arr =
      Slice.partialEqAux cmpPartialEqInst s.val arr.val := rfl

/-- `Slice.partialEqAux` with a homogeneous `PartialEq` always succeeds, and for U8
    the result `b = true ↔ xs = ys`. -/
theorem partialEqAux_U8_spec :
    ∀ (xs ys : List Std.U8),
    ∃ b : Bool, Slice.partialEqAux core.cmp.PartialEqU8 xs ys = ok b ∧
      (b = true ↔ xs = ys) := by
  intro xs
  induction xs with
  | nil =>
    intro ys; cases ys with
    | nil => exact ⟨true, by unfold Slice.partialEqAux; rfl, by simp⟩
    | cons _ _ => exact ⟨false, by unfold Slice.partialEqAux; rfl, by simp⟩
  | cons a xs ih =>
    intro ys; cases ys with
    | nil => exact ⟨false, by unfold Slice.partialEqAux; rfl, by simp⟩
    | cons c ys =>
      unfold Slice.partialEqAux
      simp only [core.cmp.PartialEqU8, liftFun2, core.cmp.impls.PartialEqU8.eq]
      by_cases hab : a = c
      · subst hab
        simp only [decide_true]
        obtain ⟨r, hr, hiff⟩ := ih ys
        exact ⟨r, by simpa using hr, by constructor <;> intro h <;> simp_all⟩
      · simp only [show decide (a = c) = false from by simp [hab]]
        exact ⟨false, by simp, by simp [hab]⟩

/-- `Slice.Insts.CoreCmpPartialEqArray.eq` with `PartialEqU8` always succeeds and
    `b = true ↔ s.val = arr.val`. -/
@[step]
theorem Slice.Insts.CoreCmpPartialEqArray.eq_U8_spec
    {N : Std.Usize}
    (s : Slice Std.U8) (arr : Array Std.U8 N) :
    Slice.Insts.CoreCmpPartialEqArray.eq core.cmp.PartialEqU8 s arr
    ⦃ b => b = true ↔ s.val = arr.val ⦄ := by
  simp only [Slice.Insts.CoreCmpPartialEqArray.eq_eq]
  have ⟨b, hb, hiff⟩ := partialEqAux_U8_spec s.val arr.val
  rw [hb]
  simp only [WP.spec_ok]
  exact hiff

/-- Implementation helper for `core.array.from_fn`
    (`[core::array::from_fn]`,
    Source: '/rustc/library/core/src/array/mod.rs', lines 109:0-111:52).

    Builds the element list by calling the closure at indices
    `i, i+1, …, i+remaining-1`, threading the mutable closure state
    through each call. -/
def core.array.from_fn_loop
    {T F : Type}
    (fnMutInst : core.ops.function.FnMut F Std.Usize T) :
    F → Std.Usize → Nat → Result (List T)
  | _, _, 0 => ok []
  | f, i, n + 1 => do
    let (val, f') ← fnMutInst.call_mut f i
    let i' ← i + 1#usize
    let rest ← core.array.from_fn_loop fnMutInst f' i' n
    ok (val :: rest)

/-- **Spec theorem for `core.array.from_fn_loop` (base case)**: when the remaining
count is `0`, the loop immediately returns the empty list `[]`. -/
@[simp]
theorem core.array.from_fn_loop_zero
    {T F : Type}
    (fnMutInst : core.ops.function.FnMut F Std.Usize T)
    (f : F) (i : Std.Usize) :
    core.array.from_fn_loop fnMutInst f i 0 = ok [] := rfl

/-- **Spec theorem for `core.array.from_fn_loop` (inductive case)**: when the remaining
count is `n + 1`, the loop calls `call_mut f i` to obtain an element `val` and updated
closure state `f'`, increments the index, recurses on the remaining `n` iterations,
and conses `val` onto the result. -/
@[simp]
theorem core.array.from_fn_loop_succ
    {T F : Type}
    (fnMutInst : core.ops.function.FnMut F Std.Usize T)
    (f : F) (i : Std.Usize) (n : Nat) :
    core.array.from_fn_loop fnMutInst f i (n + 1) =
      (do
        let (val, f') ← fnMutInst.call_mut f i
        let i' ← i + 1#usize
        let rest ← core.array.from_fn_loop fnMutInst f' i' n
        ok (val :: rest)) := rfl

/-- **Spec theorem for `core.array.from_fn_loop` (length)**: when the loop succeeds,
the resulting list has exactly `n` elements. This is proved by induction on `n`,
and requires that each index increment stays within `Usize.max`. -/
theorem core.array.from_fn_loop_length
    {T F : Type}
    (fnMutInst : core.ops.function.FnMut F Std.Usize T)
    (f : F) (i : Std.Usize) (n : Nat) (l : List T)
    (h_ok : core.array.from_fn_loop fnMutInst f i n = ok l)
    (h_bound : ↑i + n ≤ Std.Usize.max) :
    l.length = n := by
  induction n generalizing f i l with
  | zero =>
    simp only [from_fn_loop, ok.injEq, List.nil_eq] at h_ok
    subst h_ok; rfl
  | succ k ih =>
    rw [core.array.from_fn_loop_succ] at h_ok
    cases h_call : fnMutInst.call_mut f i with
    | ret vf =>
      obtain ⟨val, f'⟩ := vf
      simp only [h_call] at h_ok
      cases h_add : i + 1#usize with
      | ret i' =>
        simp only [h_add] at h_ok
        cases h_rest : core.array.from_fn_loop fnMutInst f' i' k with
        | ret rest =>
          simp only [bind_ok, uncurry_apply_pair, h_rest, ok.injEq] at h_ok
          subst h_ok
          have hi' : (↑i' : Nat) = ↑i + 1 := by
            have h_spec := Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac)
            rw [h_add, WP.spec_ok] at h_spec; scalar_tac
          simp only [List.length_cons, ih f' i' rest h_rest (by scalar_tac)]
        | vis e kk => simp [h_rest] at h_ok
        | div => simp [h_rest] at h_ok
      | vis e kk => simp [h_add] at h_ok
      | div => simp [h_add] at h_ok
    | vis e kk => simp [h_call] at h_ok
    | div => simp [h_call] at h_ok

/-- [core::array::from_fn]:
    Source: '/rustc/library/core/src/array/mod.rs', lines 109:0-111:52
    Name pattern: [core::array::from_fn]

    Concrete model of Rust's `core::array::from_fn`: creates an array of `N`
    elements where the element at index `i` is computed by calling the closure
    `f` with argument `i` (for `i = 0, 1, …, N-1`).  The closure is modelled
    as `FnMut F Usize T`, so each invocation may update the closure state.
    The outer `Result` propagates any failure from the closure calls or from
    the index arithmetic. -/
@[rust_fun "core::array::from_fn"]
def core.array.from_fn
  {T : Type} {F : Type} (N : Std.Usize) (opsfunctionFnMutFTupleUsizeTInst :
  core.ops.function.FnMut F Std.Usize T) :
  F → Result (Array T N) :=
  fun f => do
    let l ← core.array.from_fn_loop opsfunctionFnMutFTupleUsizeTInst f 0#usize N.val
    match h : decide (l.length = N.val) with
    | true => ok (Array.from l (of_decide_eq_true h))
    | false => fail .panic

/-- Helper lemma: `from_fn_loop` with a stateless closure (state = `Unit`) that always
returns `(default, ())` produces `List.replicate n default`.  This is used to discharge
the `hl` hypothesis of `from_fn_spec` for constant-valued closures such as the one in
`PolyDecoder.new_with_poly_count`. -/
theorem core.array.from_fn_loop_replicate_default
    {T : Type} [Inhabited T]
    (fnMutInst : core.ops.function.FnMut Unit Std.Usize T)
    (h_const : ∀ (i : Std.Usize), fnMutInst.call_mut () i = ok (default, ()))
    (i : Std.Usize) (n : Nat) (h_bound : ↑i + n ≤ Std.Usize.max) :
    core.array.from_fn_loop fnMutInst () i n = ok (List.replicate n default) := by
  induction n generalizing i with
  | zero => simp [core.array.from_fn_loop]
  | succ k ih =>
    simp only [core.array.from_fn_loop]
    have h_add : ∃ i', i + (1#usize : Usize) = ok i' ∧ (↑i' : Nat) = ↑i + 1 := by
      obtain ⟨i', hi', hval⟩ :=
        WP.spec_imp_exists (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
      exact ⟨i', hi', by scalar_tac⟩
    obtain ⟨i', h_eq, h_val⟩ := h_add
    have ih_eq := ih i' (by scalar_tac)
    simp [h_const, h_eq, List.replicate, ih_eq]


/-- Helper lemma: `from_fn_loop` with a *state-preserving* closure that always returns
the same value `v` (independent of the index, leaving the closure state untouched)
produces `List.replicate n v`.  Unlike `from_fn_loop_replicate_default` this works for
an arbitrary closure-state type `F` (not just `Unit`), which is needed for closures that
capture data (such as the message slice in `PolyEncoder.encode_bytes_base`). -/
theorem core.array.from_fn_loop_const
    {T F : Type}
    (fnMutInst : core.ops.function.FnMut F Std.Usize T)
    (v : T)
    (h_const : ∀ (g : F) (i : Std.Usize), fnMutInst.call_mut g i = ok (v, g))
    (f : F) (i : Std.Usize) (n : Nat) (h_bound : ↑i + n ≤ Std.Usize.max) :
    core.array.from_fn_loop fnMutInst f i n = ok (List.replicate n v) := by
  induction n generalizing f i with
  | zero => rfl
  | succ k ih =>
    simp only [core.array.from_fn_loop, h_const]
    have h_add : ∃ i', i + (1#usize : Usize) = ok i' ∧ (↑i' : Nat) = ↑i + 1 := by
      obtain ⟨i', hi', hval⟩ :=
        WP.spec_imp_exists (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
      exact ⟨i', hi', by scalar_tac⟩
    obtain ⟨i', h_eq, h_val⟩ := h_add
    simp [h_eq, ih f i' (by scalar_tac), List.replicate]

/-- **Spec theorem for `core::array::from_fn`**: when the loop helper
`core.array.from_fn_loop` succeeds and produces a list `l` of length `N`,
the result is an array whose underlying list is `l`.  The per-element
behaviour is definitional in the `FnMut` instance. -/
@[step]
theorem core.array.from_fn_spec
    {T F : Type} (N : Std.Usize)
    (fnMutInst : core.ops.function.FnMut F Std.Usize T)
    (f : F)
    (l : List T)
    (hl : core.array.from_fn_loop fnMutInst f 0#usize N.val = ok l)
    (hlen : l.length = N.val) :
    core.array.from_fn N fnMutInst f
      ⦃ (arr : Array T N) => arr.val = l ⦄ := by
  simp [core.array.from_fn, hl]
  split
  · simp_all
  · simp_all


namespace Shared0T.Insts.CoreBorrowBorrow
/-- [core::borrow::{core::borrow::Borrow<T> for &0 (T)}::borrow]:
    Source: '/rustc/library/core/src/borrow.rs', lines 230:4-230:26
    Name pattern: [core::borrow::{core::borrow::Borrow<&'0 @T, @T>}::borrow]

    Concrete model of Rust's `<&T as Borrow<&T>>::borrow` for a shared reference `&T`:
    borrowing simply returns the value unchanged.  The outer `Result` is
    always `ok` (the call never panics). -/
@[rust_fun "core::borrow::{core::borrow::Borrow<&'0 @T, @T>}::borrow"]
def borrow {T : Type} (x : T): Result T := ok x

/-- **Spec theorem for `<&T as Borrow<&T>>::borrow`**: borrowing returns the value unchanged. -/
@[step]
theorem borrow_spec {T : Type} (x : T) :
    borrow x ⦃ result => result = x ⦄ := by
  simp [borrow]

end Shared0T.Insts.CoreBorrowBorrow

namespace U32.Insts.CoreConvertTryFromU64TryFromIntError
open core.num.error
/-- [core::convert::num::{core::convert::TryFrom<u64, core::num::error::TryFromIntError> for u32}::try_from]:
    Source: '/rustc/library/core/src/convert/num.rs', lines 294:12-294:64
    Name pattern: [core::convert::num::{core::convert::TryFrom<u32, u64, core::num::error::TryFromIntError>}::try_from]

    Concrete model of Rust's `<u32 as TryFrom<u64>>::try_from`: the conversion succeeds with
    `Ok v` (where `v.val = value.val`) exactly when `value` fits in a `u32`
    (`value.val ≤ u32::MAX`), and otherwise returns `Err` carrying a
    `TryFromIntError`.  The outer `Result` is always `ok` (the call never
    panics). -/
@[rust_fun
  "core::convert::num::{core::convert::TryFrom<u32, u64, core::num::error::TryFromIntError>}::try_from"]
def try_from (value : Std.U64) : Result (core.result.Result Std.U32 TryFromIntError) :=
    match UScalar.tryMkOpt .U32 value.val with
    | some v => ok (core.result.Result.Ok v)
    | none   => ok (core.result.Result.Err ())

-- /-- **Spec theorem for `<<u32> as TryFrom<u64>>::try_from`**
-- * if `value.val ≤ U32.max` the result is `Ok v` with `v.val = value.val`;
-- * otherwise the result is `Err`. -/
@[step]
theorem try_from_spec (value : U64) :
    try_from value ⦃ (r : core.result.Result U32 TryFromIntError) =>
      match r with
      | .Ok v => value.val ≤ U32.max ∧ v.val = value.val
      | .Err _ => ¬ value.val ≤ U32.max ⦄ := by
  unfold try_from
  have htry := UScalar.tryMkOpt_eq .U32 value.val
  step*

end U32.Insts.CoreConvertTryFromU64TryFromIntError

/-- [core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field2_finish]:
    Source: '/rustc/library/core/src/fmt/mod.rs', lines 2466:4-2473:15
    Name pattern: [core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field2_finish] -/
@[rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field2_finish"]
noncomputable opaque core.fmt.Formatter.debug_struct_field2_finish
  :
  core.fmt.Formatter → Str → Str → Dyn (fun _dyn => core.fmt.Debug _dyn)
    → Str → Dyn (fun _dyn => core.fmt.Debug _dyn) → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [core::fmt::{core::fmt::Display for &0 (T)}::fmt]:
    Source: '/rustc/library/core/src/fmt/mod.rs', lines 2865:12-2865:58
    Name pattern: [core::fmt::{core::fmt::Display<&'0 @T>}::fmt] -/
@[rust_fun "core::fmt::{core::fmt::Display<&'0 @T>}::fmt"]
noncomputable opaque Shared0T.Insts.CoreFmtDisplay.fmt
  {T : Type} (DisplayInst : core.fmt.Display T) :
  T → core.fmt.Formatter → Result ((core.result.Result Unit core.fmt.Error)
    × core.fmt.Formatter)

/-- [core::hint::black_box]:
    Source: '/rustc/library/core/src/hint.rs', lines 490:0-490:40
    Name pattern: [core::hint::black_box] -/
@[rust_fun "core::hint::black_box"]
def core.hint.black_box {T : Type} : T → Result T :=
  fun x => ok x

/-- **Spec theorem for `core::hint::black_box`**: `black_box` is documented as
an identity function on values; its compile-time effect in Rust is making its
argument opaque to the optimiser, which has no semantic content in the Lean model. -/
@[step]
theorem core.hint.black_box_spec {T : Type} (x : T) :
    core.hint.black_box x ⦃ (r : T) => r = x ⦄ := by
  simp [core.hint.black_box]

namespace core.iter
namespace traits.iterator.Iterator

-- Since `next` is often the only custom method, we define a way to construct an entire
-- `Iterator` from just the `next` function, and populate the rest with defaults.
def fromNext
  {Self: Type} {Self_Item: Type}
  (nextFn: Self → Result ((Option Self_Item) × Self)) :
  core.iter.traits.iterator.Iterator Self Self_Item :=
  {
    next := nextFn,
    step_by := core.iter.traits.iterator.Iterator.step_by.default,
    enumerate := core.iter.traits.iterator.Iterator.enumerate.default,
    take := core.iter.traits.iterator.Iterator.take.default
  }

end traits.iterator.Iterator

namespace adapters.map

def mapIteratorTransformer
  {I: Type} {A: Type} {B: Type} {F: Type}
  (map: core.iter.adapters.map.Map I F)
  (iterImpl: core.iter.traits.iterator.Iterator I A)
  (fnImpl: core.ops.function.FnMut F A B) :
  core.iter.traits.iterator.Iterator I B :=
    -- we define the `next` behavior of the mapped-over iterator:
    let mapNext (iter: I) : Result ((Option B) × I) := do
      -- advance underlying iterator
      let (opt, iter') ← iterImpl.next iter
      match opt with
      | none => ok (none, iter') -- If done, nothing to map over
      | some val =>
        -- If underlying iterator returns x, compute f(x). This may fail or diverge
        let (postFnVal, _) ← fnImpl.call_mut map.f val
        -- if execution reaches here, call_mut did not return div or fail
        ok (some postFnVal, iter')
    traits.iterator.Iterator.fromNext mapNext

end adapters.map
end core.iter

/-- [core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<(usize, Clause0_Item)> for core::iter::adapters::enumerate::Enumerate<I>}::next]:
    Source: '/rustc/library/core/src/iter/adapters/enumerate.rs', lines 79:4-79:64
    Name pattern: [core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<core::iter::adapters::enumerate::Enumerate<@I>, (usize, @Clause0_Item)>}::next]

    Concrete model of Rust's `Enumerate<I>::next`: retrieves the next element from the
    underlying iterator, pairs it with the current count, and increments the count using
    wrapping addition (matching Rust's std library semantics where the count increment
    is explicitly wrapping and cannot fail). -/
@[rust_fun
  "core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<core::iter::adapters::enumerate::Enumerate<@I>, (usize, @Clause0_Item)>}::next"]
def
  core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
  {I : Type} {Clause0_Item : Type} (traitsiteratorIteratorInst :
  core.iter.traits.iterator.Iterator I Clause0_Item) :
  core.iter.adapters.enumerate.Enumerate I → Result ((Option (Std.Usize ×
    Clause0_Item)) × (core.iter.adapters.enumerate.Enumerate I)) :=
  fun self => do
    let (opt, iter') ← traitsiteratorIteratorInst.next self.iter
    match opt with
    | none => ok (none, ⟨iter', self.count⟩)
    | some val =>
      let i := self.count
      let count' ← i + 1#usize
      ok (some (i, val), ⟨iter', count'⟩)

/-- [core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<(usize, Clause0_Item)> for core::iter::adapters::enumerate::Enumerate<I>}::enumerate]:
    Source: '/rustc/library/core/src/iter/adapters/enumerate.rs', lines 62:0-64:16
    Name pattern: [core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<core::iter::adapters::enumerate::Enumerate<@I>, (usize, @Clause0_Item)>}::enumerate] -/
@[rust_fun
  "core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<core::iter::adapters::enumerate::Enumerate<@I>, (usize, @Clause0_Item)>}::enumerate"]
def
  core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.enumerate
  {I : Type} {Clause0_Item : Type}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (self: core.iter.adapters.enumerate.Enumerate I):
  Result (core.iter.adapters.enumerate.Enumerate (core.iter.adapters.enumerate.Enumerate I)) :=
    core.iter.traits.iterator.Iterator.enumerate.default self

/-- [core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<(usize, Clause0_Item)> for core::iter::adapters::enumerate::Enumerate<I>}::map]:
    Source: '/rustc/library/core/src/iter/adapters/enumerate.rs', lines 62:0-64:16
    Name pattern: [core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<core::iter::adapters::enumerate::Enumerate<@I>, (usize, @Clause0_Item)>}::map] -/
@[rust_fun
  "core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<core::iter::adapters::enumerate::Enumerate<@I>, (usize, @Clause0_Item)>}::map"]
def
  core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.map
  {I : Type} {B : Type} {F : Type} {Clause0_Item : Type}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
  (opsfunctionFnMutFTuplePairUsizeClause0_ItemBInst : core.ops.function.FnMut F (Std.Usize × Clause0_Item) B)
  (self: core.iter.adapters.enumerate.Enumerate I)
  (fn: F) : Result (core.iter.adapters.map.Map (core.iter.adapters.enumerate.Enumerate I) F) :=
    -- The `.map` operation merely stores information that is computed on demand, so it cannot fail
    ok ({iter := self, f := fn})

/-- [core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<(usize, Clause0_Item)> for core::iter::adapters::enumerate::Enumerate<I>}::step_by]:
    Source: '/rustc/library/core/src/iter/adapters/enumerate.rs', lines 62:0-64:16
    Name pattern: [core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<core::iter::adapters::enumerate::Enumerate<@I>, (usize, @Clause0_Item)>}::step_by] -/
@[rust_fun
  "core::iter::adapters::enumerate::{core::iter::traits::iterator::Iterator<core::iter::adapters::enumerate::Enumerate<@I>, (usize, @Clause0_Item)>}::step_by"]
def
  core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.step_by
  {I : Type} {Clause0_Item : Type}
  (traitsiteratorIteratorInst: core.iter.traits.iterator.Iterator I Clause0_Item)
  (self: core.iter.adapters.enumerate.Enumerate I)
  (n: Std.Usize):
    Result (core.iter.adapters.step_by.StepBy (core.iter.adapters.enumerate.Enumerate I)) :=
      core.iter.traits.iterator.Iterator.step_by.default self n

/-- [core::iter::adapters::map::{core::iter::traits::iterator::Iterator<B> for core::iter::adapters::map::Map<I, F>}::collect]:
    Source: '/rustc/library/core/src/iter/adapters/map.rs', lines 99:0-101:27
    Name pattern: [core::iter::adapters::map::{core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>}::collect] -/
@[rust_fun
  "core::iter::adapters::map::{core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>}::collect"]
def core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect
  {B : Type} {I : Type} {F : Type} {B1 : Type} {Clause0_Item : Type}
  (traitsiteratorIteratorInst: core.iter.traits.iterator.Iterator I Clause0_Item)
  (opsfunctionFnMutFTupleClause0_ItemBInst: core.ops.function.FnMut F Clause0_Item B)
  (traitscollectFromIteratorInst: core.iter.traits.collect.FromIterator B1 B)
  (map: core.iter.adapters.map.Map I F): Result B1 :=
    core.iter.traits.iterator.Iterator.collect.default
      -- mapIteratorTransformer turns an A-iterator into a B-iterator, given f: A → B
      (mapIteratorTransformer map traitsiteratorIteratorInst opsfunctionFnMutFTupleClause0_ItemBInst)
      traitscollectFromIteratorInst
      map.iter


namespace I32.Insts.CoreIterRangeStep
/-- [core::iter::range::{core::iter::range::Step for i32}::backward_checked]:
    Source: '/rustc/library/core/src/iter/range.rs', lines 340:16-340:74
    Name pattern: [core::iter::range::{core::iter::range::Step<i32>}::backward_checked]

    Concrete model of Rust's `Step::backward_checked` for `i32`:
    given `start : i32` and `count : usize`, compute the integer difference
    `start - count` and return `Some(result)` if it fits in `i32`,
    `None` otherwise.  The outer `Result` is always `ok` (the call
    never panics). -/
@[rust_fun
  "core::iter::range::{core::iter::range::Step<i32>}::backward_checked"]
def backward_checked (start: Std.I32) (n : Std.Usize) : Result (Option Std.I32) :=
  ok (IScalar.tryMkOpt .I32 (start.val - n.val))

/-- **Spec theorem for `Step<i32>::backward_checked` with an arbitrary step `n`**

- Since `n.val ≥ 0`, the difference `start.val - n.val ≤ start.val ≤ I32.max` always satisfies the
  upper bound, so only the lower bound is relevant.
- If `I32.min ≤ start.val - n.val` the returned option is `some z` with `z.val = start.val - n.val`.
- Otherwise the returned option is `none`. -/
@[step]
theorem backward_checked_spec (start : I32) (n : Usize) :
    backward_checked start n ⦃ (opt : Option I32) =>
      match opt with
      | some z => I32.min ≤ start.val - n.val ∧ z.val = start.val - n.val
      | none   => ¬ I32.min ≤ start.val - n.val ⦄ := by
  unfold  I32.Insts.CoreIterRangeStep.backward_checked
  have htry := IScalar.tryMkOpt_eq .I32 (start.val - ↑n.val)
  step*
  grind

/-- [core::iter::range::{core::iter::range::Step for i32}::forward_checked]:
    Source: '/rustc/library/core/src/iter/range.rs', lines 319:16-319:73
    Name pattern: [core::iter::range::{core::iter::range::Step<i32>}::forward_checked]

    Concrete model of Rust's `Step::forward_checked` for `i32`:
    given `start : i32` and `count : usize`, compute the integer sum
    `start + count` and return `Some(result)` if it fits in `i32`,
    `None` otherwise.  The outer `Result` is always `ok` (the call
    never panics). -/
@[rust_fun
  "core::iter::range::{core::iter::range::Step<i32>}::forward_checked"]
def forward_checked (start: Std.I32) (n : Std.Usize) : Result (Option Std.I32) :=
  ok (IScalar.tryMkOpt .I32 (start.val + n.val))

/-- **Spec theorem for `Step<i32>::forward_checked` with an arbitrary step `n`**

- Since `n.val ≥ 0`, the sum `start.val + n.val ≥ start.val ≥ I32.min` always satisfies the lower
  bound, so only the upper bound is relevant.
- If `start.val + n.val ≤ I32.max` the returned option is `some z` with `z.val = start.val + n.val`;
- Otherwise the returned option is `none`. -/
@[step]
theorem forward_checked_spec (start : I32) (n : Usize) :
    forward_checked start n ⦃ (opt : Option I32) =>
      match opt with
      | some z => start.val + n.val ≤ I32.max ∧ z.val = start.val + n.val
      | none   => ¬ start.val + n.val ≤ I32.max ⦄ := by
  suffices h : ∃ opt,
      I32.Insts.CoreIterRangeStep.forward_checked start n = ok opt ∧
      (start.val + n.val ≤ I32.max →
          ∃ z, opt = some z ∧ z.val = start.val + n.val) ∧
      (¬ start.val + n.val ≤ I32.max → opt = none) by grind
  unfold  I32.Insts.CoreIterRangeStep.forward_checked
  have htry := IScalar.tryMkOpt_eq .I32 (start.val + ↑n.val)
  generalize IScalar.tryMkOpt .I32 (start.val + ↑n.val) = opt at htry ⊢
  cases opt with
  | none => grind
  | some z =>
    refine ⟨some z, rfl, fun _ => ⟨z, rfl, by grind⟩, fun h => by grind⟩

/-- [core::iter::range::{core::iter::range::Step for i32}::steps_between]:
    Source: '/rustc/library/core/src/iter/range.rs', lines 304:16-304:84
    Name pattern: [core::iter::range::{core::iter::range::Step<i32>}::steps_between]

    Concrete model of Rust's `Step::steps_between` for `i32`:
    given `start : i32` and `end_ : i32`, if `start ≤ end_` the number of steps `end_ - start` is
    a non-negative integer that always fits in `usize` (since `i32` is no wider
    than `usize`), so the result is `(d, some d)` with `d = end_ - start`; otherwise the
    result is `(0, none)`.  The outer `Result` is always `ok` (the call never
    panics). -/
@[rust_fun "core::iter::range::{core::iter::range::Step<i32>}::steps_between"]
def steps_between (start end_ : Std.I32) : Result (Std.Usize × (Option Std.Usize)) :=
    if start.val ≤ end_.val then
      let o := UScalar.tryMkOpt .Usize (end_.val - start.val).toNat
      ok (o.getD 0#usize, o)
    else
      ok (0#usize, none)

/-- **Spec theorem for `Step<i32>::steps_between`**
- If `start.val ≤ end_.val` the result is `(diff, some diff)` with
  `diff.val = (end_.val - start.val).toNat`. The `none` branch is `False`: since
  `i32` is no wider than `usize`, `diff = end_.val - start.val` always fits in
  `usize`, so `UScalar.tryMkOpt` always returns `some` and the `none` case is
  not accessible.
- Otherwise the result is `(0, none)`. -/
@[step]
theorem steps_between_spec (start end_ : I32) :
    steps_between start end_ ⦃ (result : Usize × Option Usize) =>
      if start.val ≤ end_.val then
        let diff := (end_.val - start.val).toNat
        match result.2 with
        | some hi => diff ≤ Usize.max ∧ result.1.val = diff ∧ hi.val = diff
        | none    => False
      else
        result.1.val = 0 ∧ result.2 = none ⦄ := by
  unfold steps_between
  have htry := UScalar.tryMkOpt_eq .Usize ((end_.val - start.val).toNat)
  step*
  grind

end I32.Insts.CoreIterRangeStep

/-- [core::ops::range::{core::ops::range::RangeBounds<T> for core::ops::range::RangeFrom<T>}::end_bound]:
    Source: '/rustc/library/core/src/ops/range.rs', lines 1071:4-1071:36
    Name pattern: [core::ops::range::{core::ops::range::RangeBounds<core::ops::range::RangeFrom<@T>, @T>}::end_bound] -/
@[rust_fun
  "core::ops::range::{core::ops::range::RangeBounds<core::ops::range::RangeFrom<@T>, @T>}::end_bound"]
def core.ops.range.RangeFrom.Insts.CoreOpsRangeRangeBounds.end_bound
  {T : Type} : core.ops.range.RangeFrom T → Result (core.ops.range.Bound T) :=
  fun _ => ok .Unbounded

/-- **Spec theorem for `RangeBounds<RangeFrom>::end_bound`**: a `start..` range is
unbounded above. -/
@[step]
theorem core.ops.range.RangeFrom.Insts.CoreOpsRangeRangeBounds.end_bound_spec
    {T : Type} (rf : core.ops.range.RangeFrom T) :
    core.ops.range.RangeFrom.Insts.CoreOpsRangeRangeBounds.end_bound rf
      ⦃ b => b = .Unbounded ⦄ := by
  simp [core.ops.range.RangeFrom.Insts.CoreOpsRangeRangeBounds.end_bound]

/-- [core::ops::range::{core::ops::range::RangeBounds<T> for core::ops::range::RangeFrom<T>}::start_bound]:
    Source: '/rustc/library/core/src/ops/range.rs', lines 1068:4-1068:38
    Name pattern: [core::ops::range::{core::ops::range::RangeBounds<core::ops::range::RangeFrom<@T>, @T>}::start_bound] -/
@[rust_fun
  "core::ops::range::{core::ops::range::RangeBounds<core::ops::range::RangeFrom<@T>, @T>}::start_bound"]
def core.ops.range.RangeFrom.Insts.CoreOpsRangeRangeBounds.start_bound
  {T : Type} : core.ops.range.RangeFrom T → Result (core.ops.range.Bound T) :=
  fun rf => ok (.Included rf.start)

/-- **Spec theorem for `RangeBounds<RangeFrom>::start_bound`**: a `start..` range is
bounded below, inclusively, by `start`. -/
@[step]
theorem core.ops.range.RangeFrom.Insts.CoreOpsRangeRangeBounds.start_bound_spec
    {T : Type} (rf : core.ops.range.RangeFrom T) :
    core.ops.range.RangeFrom.Insts.CoreOpsRangeRangeBounds.start_bound rf
      ⦃ b => b = .Included rf.start ⦄ := by
  simp [core.ops.range.RangeFrom.Insts.CoreOpsRangeRangeBounds.start_bound]

/-- [core::option::{core::option::Option<T>}::as_ref]:
    Source: '/rustc/library/core/src/option.rs', lines 744:4-744:44
    Name pattern: [core::option::{core::option::Option<@T>}::as_ref] -/
@[rust_fun "core::option::{core::option::Option<@T>}::as_ref"]
def core.option.Option.as_ref {T : Type} : Option T → Result (Option T) :=
  fun o => ok o

/-- **Spec theorem for `Option::as_ref`**: references are transparent in the Lean
model, so `as_ref` is the identity. -/
@[step]
theorem core.option.Option.as_ref_spec {T : Type} (o : Option T) :
    core.option.Option.as_ref o ⦃ r => r = o ⦄ := by
  simp [core.option.Option.as_ref]

/-- [core::option::{core::option::Option<T>}::ok_or]:
    Source: '/rustc/library/core/src/option.rs', lines 1337:4-1337:73
    Name pattern: [core::option::{core::option::Option<@T>}::ok_or] -/
@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or
  {T : Type} {E : Type} : Option T → E → Result (core.result.Result T E) :=
  fun o e =>
    match o with
    | some v => ok (.Ok v)
    | none => ok (.Err e)

/-- **Spec theorem for `Option::ok_or`**: `some v` becomes `Ok v`; `none` becomes
`Err e`. -/
@[step]
theorem core.option.Option.ok_or_spec {T E : Type} (o : Option T) (e : E) :
    core.option.Option.ok_or o e ⦃ r => r = o.elim (.Err e) .Ok ⦄ := by
  rcases o with _ | v <;> simp [core.option.Option.ok_or]

/-- [core::option::{core::clone::Clone for core::option::Option<T>}::clone]:
    Source: '/rustc/library/core/src/option.rs', lines 2261:4-2261:27
    Name pattern: [core::option::{core::clone::Clone<core::option::Option<@T>>}::clone] -/
@[rust_fun
  "core::option::{core::clone::Clone<core::option::Option<@T>>}::clone"]
noncomputable opaque core.option.Option.Insts.CoreCloneClone.clone
  {T : Type} (cloneCloneInst : core.clone.Clone T) :
  Option T → Result (Option T)

/-- [core::option::{core::default::Default for core::option::Option<T>}::default]:
    Source: '/rustc/library/core/src/option.rs', lines 2297:4-2297:29
    Name pattern: [core::option::{core::default::Default<core::option::Option<@T>>}::default] -/
@[rust_fun
  "core::option::{core::default::Default<core::option::Option<@T>>}::default"]
noncomputable opaque core.option.Option.Insts.CoreDefaultDefault.default
  (T : Type) : Result (Option T)

/-- [core::option::{core::cmp::PartialEq<core::option::Option<T>> for core::option::Option<T>}::eq]:
    Source: '/rustc/library/core/src/option.rs', lines 2424:4-2424:38
    Name pattern: [core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq] -/
@[rust_fun
  "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq"]
def core.option.Option.Insts.CoreCmpPartialEqOption.eq
  {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) :
  Option T → Option T → Result Bool :=
  fun o1 o2 =>
    match o1, o2 with
    | some a, some b => cmpPartialEqInst.eq a b
    | none, none => ok true
    | _, _ => ok false

/-- **Spec theorem for `PartialEq::eq` on `Option<T>`**: structural equality —
`none = none` is `true`, a `some`/`none` mismatch is `false`, and `some a = some b`
delegates to the element instance `cmpPartialEqInst.eq a b`. -/
@[simp]
theorem core.option.Option.Insts.CoreCmpPartialEqOption.eq_eq
    {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) (o1 o2 : Option T) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq cmpPartialEqInst o1 o2 =
      match o1, o2 with
      | some a, some b => cmpPartialEqInst.eq a b
      | none, none => ok true
      | _, _ => ok false := by
  rfl

/-- [core::result::{core::result::Result<T, E>}::is_ok]:
    Source: '/rustc/library/core/src/result.rs', lines 593:4-593:37
    Name pattern: [core::result::{core::result::Result<@T, @E>}::is_ok] -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::is_ok"]
def core.result.Result.is_ok
  {T : Type} {E : Type} : core.result.Result T E → Result Bool :=
  fun r =>
    match r with
    | .Ok _ => ok true
    | .Err _ => ok false

/-- **Spec theorem for `Result::is_ok`**: `true` on `Ok`, `false` on `Err`. -/
@[step]
theorem core.result.Result.is_ok_spec {T E : Type} (r : core.result.Result T E) :
    core.result.Result.is_ok r ⦃ b =>
      b = match r with | .Ok _ => true | .Err _ => false ⦄ := by
  rcases r with v | e <;> simp [core.result.Result.is_ok]

/-- [core::result::{core::result::Result<T, E>}::map_err]:
    Source: '/rustc/library/core/src/result.rs', lines 962:4-964:53
    Name pattern: [core::result::{core::result::Result<@T, @E>}::map_err] -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err
  {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
  core.ops.function.FnOnce O E F) :
  core.result.Result T E → O → Result (core.result.Result T F) :=
  fun r op =>
    match r with
    | .Ok v => ok (.Ok v)
    | .Err e => do
      let f ← opsfunctionFnOnceOTupleEFInst.call_once op e
      ok (.Err f)

/-- **Spec theorems for `Result::map_err`**: `Ok` is unchanged; `Err e` applies the
closure to `e` via `FnOnce::call_once`. The `Err` behaviour is definitional in the
closure, so these are stated as unfolding lemmas on the constructors. -/
@[simp]
theorem core.result.Result.map_err_Ok
    {T E F O : Type} (inst : core.ops.function.FnOnce O E F) (v : T) (op : O) :
    core.result.Result.map_err inst (.Ok v) op = ok (.Ok v) := rfl

@[simp]
theorem core.result.Result.map_err_Err
    {T E F O : Type} (inst : core.ops.function.FnOnce O E F) (e : E) (op : O) :
    core.result.Result.map_err (T := T) inst (.Err e) op =
      (do let f ← inst.call_once op e; ok (.Err f)) := rfl

/-- Implementation helper for `Slice.Insts.CoreCmpOrd.cmp`
(`[core::slice::cmp::{core::cmp::Ord<[@T]>}::cmp]`,
Source: '/rustc/library/core/src/slice/cmp.rs', lines 37:4-37:42).

Lexicographic comparison of two element lists, delegating per-element to the
`Ord` instance and short-circuiting on the first non-`eq` result. -/
def Slice.lexCmpAux {T : Type} (cmpOrdInst : core.cmp.Ord T) :
    List T → List T → Result Ordering
  | [], [] => ok .eq
  | [], _ :: _ => ok .lt
  | _ :: _, [] => ok .gt
  | a :: xs, b :: ys => do
    let o ← cmpOrdInst.cmp a b
    match o with
    | .eq => Slice.lexCmpAux cmpOrdInst xs ys
    | o => ok o

/-- [core::slice::cmp::{core::cmp::Ord for [T]}::cmp]:
    Source: '/rustc/library/core/src/slice/cmp.rs', lines 37:4-37:42
    Name pattern: [core::slice::cmp::{core::cmp::Ord<[@T]>}::cmp] -/
@[rust_fun "core::slice::cmp::{core::cmp::Ord<[@T]>}::cmp"]
def Slice.Insts.CoreCmpOrd.cmp
  {T : Type} (cmpOrdInst : core.cmp.Ord T) :
  Slice T → Slice T → Result Ordering :=
  fun s1 s2 => Slice.lexCmpAux cmpOrdInst s1.val s2.val

/-- **Spec theorem for `Ord::cmp` on `[T]`**: lexicographic comparison over the
elements. The per-element behaviour is definitional in the `Ord` instance, so this
exposes the comparison as the list helper `Slice.lexCmpAux`. -/
@[simp]
theorem Slice.Insts.CoreCmpOrd.cmp_eq
    {T : Type} (cmpOrdInst : core.cmp.Ord T) (s1 s2 : Slice T) :
    Slice.Insts.CoreCmpOrd.cmp cmpOrdInst s1 s2 =
      Slice.lexCmpAux cmpOrdInst s1.val s2.val := rfl

/-- [core::slice::{[T]}::binary_search]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 2934:4-2936:23
    Name pattern: [core::slice::{[@T]}::binary_search]
    On a match Rust returns the index of *some* equal element
    (which one is unspecified), and `Err` carries the insertion point. -/
@[rust_fun "core::slice::{[@T]}::binary_search"]
noncomputable opaque core.slice.Slice.binary_search
  {T : Type} (cmpOrdInst : core.cmp.Ord T) :
  Slice T → T → Result (core.result.Result Std.Usize Std.Usize)

/-- [core::slice::index::{core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::index_mut]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 660:4-660:51
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index_mut] -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index_mut"]
def
  core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut
  {T : Type} :
  core.ops.range.RangeFull → Slice T → Result ((Slice T) × (Slice T →
    Slice T)) :=
  fun _ s => ok (s, fun s' => s')

/-- **Spec theorem for `SliceIndex<RangeFull>::index_mut`**: the whole-slice
mutable borrow returns the slice unchanged with an identity write-back. -/
@[step]
theorem core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut_spec
    {T : Type} (r : core.ops.range.RangeFull) (s : Slice T) :
    core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut r s
      ⦃ (s', back) => s' = s ∧ ∀ x, back x = x ⦄ := by
  simp [core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]

/-- [core::slice::index::{core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::index]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 655:4-655:39
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index] -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index"]
def core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index
  {T : Type} : core.ops.range.RangeFull → Slice T → Result (Slice T) :=
  fun _ s => ok s

/-- **Spec theorem for `SliceIndex<RangeFull>::index`**: indexing by `..` returns
the whole slice unchanged. -/
@[step]
theorem core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_spec
    {T : Type} (r : core.ops.range.RangeFull) (s : Slice T) :
    core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index r s
      ⦃ r' => r' = s ⦄ := by
  simp [core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]

/-- [core::slice::index::{core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::get_mut]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 640:4-640:57
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_mut] -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_mut"]
def core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut
  {T : Type} :
  core.ops.range.RangeFull → Slice T → Result ((Option (Slice T)) ×
    (Option (Slice T) → Slice T)) :=
  fun _ s => ok (some s, fun o => o.getD s)

/-- **Spec theorem for `SliceIndex<RangeFull>::get_mut`**: the whole slice is always
in bounds, so this returns `some s` plus a write-back that installs the new slice
(keeping the original when given `none`). -/
@[step]
theorem core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut_spec
    {T : Type} (r : core.ops.range.RangeFull) (s : Slice T) :
    core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut r s
      ⦃ (o, back) => o = some s ∧ ∀ x, back x = x.getD s ⦄ := by
  simp [core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut]

/-- [core::slice::index::{core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::get]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 635:4-635:45
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get] -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get"]
def core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get
  {T : Type} :
  core.ops.range.RangeFull → Slice T → Result (Option (Slice T)) :=
  fun _ s => ok (some s)

/-- **Spec theorem for `SliceIndex<RangeFull>::get`**: the whole slice is always in
bounds, so `get` by `..` returns `some s`. -/
@[step]
theorem core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_spec
    {T : Type} (r : core.ops.range.RangeFull) (s : Slice T) :
    core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get r s
      ⦃ o => o = some s ⦄ := by
  simp [core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get]

/-- [core::slice::iter::{core::iter::traits::iterator::Iterator<&'a (T)> for core::slice::iter::Iter<'a, T>}::map]:
    Source: '/rustc/library/core/src/slice/iter/macros.rs', lines 153:8-153:45
    Name pattern: [core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::map] -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::map"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.map
  {T : Type} {B : Type} {F : Type}
  (opsfunctionFnMutFTupleSharedATBInst: core.ops.function.FnMut F T B)
  (iter: core.slice.iter.Iter T)
  (fn: F): Result (core.iter.adapters.map.Map (core.slice.iter.Iter T) F) :=
    ok {iter := iter, f:= fn}

@[step]
theorem sharedAT_map_spec {T : Type} {B : Type} {F : Type} (opsfunctionFnMutFTupleSharedATBInst:
    core.ops.function.FnMut F T B)
    (iter: core.slice.iter.Iter T) (fn: F) :
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.map
      opsfunctionFnMutFTupleSharedATBInst iter fn
      ⦃ (map : (core.iter.adapters.map.Map (core.slice.iter.Iter T) F)) =>
      map.f = fn ∧ map.iter = iter ⦄ := by
  unfold core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.map
  simp [WP.spec_ok]

/-- [core::slice::iter::{core::iter::traits::collect::IntoIterator<&'a (T), core::slice::iter::Iter<'a, T>> for &'a ([T])}::into_iter]:
    Source: '/rustc/library/core/src/slice/iter.rs', lines 25:4-25:37
    Name pattern: [core::slice::iter::{core::iter::traits::collect::IntoIterator<&'a [@T], &'a @T, core::slice::iter::Iter<'a, @T>>}::into_iter] -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::collect::IntoIterator<&'a [@T], &'a @T, core::slice::iter::Iter<'a, @T>>}::into_iter"]
def
  SharedASlice.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
  {T : Type} : Slice T → Result (core.slice.iter.Iter T) :=
  fun s => ok ⟨s, 0⟩

@[step]
theorem into_iter_spec {T : Type} (s : Slice T) :
    SharedASlice.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
      s
      ⦃ (iter : core.slice.iter.Iter T) =>
      iter.slice = s ∧ iter.i = 0 ⦄ := by
  unfold SharedASlice.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
  simp [WP.spec_ok]

/-- [core::result::{core::result::Result<T, E>}::ok]:
    Source: '/rustc/library/core/src/result.rs', lines 708:4-711:28
    Name pattern: [core::result::{core::result::Result<@T, @E>}::ok]
    Visibility: public
    Rust's Result::ok() method: converts Result<T,E> to Option<T>, discarding the error. -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::ok"]
def core.result.Result.ok {T E : Type} (r : core.result.Result T E) :
    Result (Option T) :=
  match r with
  | core.result.Result.Ok v => _root_.Aeneas.Std.Result.ok (some v)
  | core.result.Result.Err _ => _root_.Aeneas.Std.Result.ok none

namespace core.slice.Slice

/-- [core::slice::{[T]}::clone_from_slice]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 4254:4-4256:44
    Name pattern: [core::slice::{[@T]}::clone_from_slice] -/
@[rust_fun "core::slice::{[@T]}::clone_from_slice"]
def clone_from_slice {T : Type} (cloneCloneInst : core.clone.Clone T) :
  Slice T → Slice T → Result (Slice T) :=
  fun dst src =>
    -- Rust panics when the destination and source lengths differ.
    if dst.length = src.length then Slice.clone cloneCloneInst.clone src
    else fail .panic

/-- **Spec theorem for `<[T]>::clone_from_slice`**: requires the destination and source to have
equal length (Rust panics otherwise); when the element `Clone` instance acts as the identity
(the usual case), the destination becomes a copy of the source. -/
@[step]
theorem clone_from_slice_spec {T : Type} (cloneCloneInst : core.clone.Clone T) (dst src : Slice T)
    (hlen : dst.length = src.length) (h : ∀ x ∈ src.val, cloneCloneInst.clone x = ok x) :
    clone_from_slice cloneCloneInst dst src ⦃ (r : Slice T) => src = r ⦄ := by
  simpa [clone_from_slice, ite_eq_left hlen] using Slice.clone_spec h

/-- `clone_from_slice` for `u8` copies the source slice into the destination, returning a slice
whose contents and length equal those of the source. Requires the destination and source to have
equal length (Rust panics otherwise). -/
@[step]
lemma clone_from_slice_U8_spec (dst src : Slice Std.U8) (hlen : dst.length = src.length) :
    clone_from_slice core.clone.CloneU8 dst src ⦃ (result : Slice U8) =>
      result.val = src.val ∧ result.length = src.length ⦄ := by
  unfold clone_from_slice
  step*

end core.slice.Slice

/-- Implementation helper for `core.slice.Slice.copy_within`
(`[core::slice::{[@T]}::copy_within]`,
Source: '/rustc/library/core/src/slice/mod.rs', lines 4354:4-4356:16).

Resolve a `RangeBounds` lower bound to a concrete start index. -/
def Slice.copyWithinStart (b : core.ops.range.Bound Std.Usize) : Nat :=
  match b with
  | .Included i => i.val
  | .Excluded i => i.val + 1
  | .Unbounded => 0

/-- Implementation helper for `core.slice.Slice.copy_within`
(`[core::slice::{[@T]}::copy_within]`,
Source: '/rustc/library/core/src/slice/mod.rs', lines 4354:4-4356:16).

Resolve a `RangeBounds` upper bound to a concrete end index (`len` when open). -/
def Slice.copyWithinEnd (b : core.ops.range.Bound Std.Usize) (len : Nat) : Nat :=
  match b with
  | .Included i => i.val + 1
  | .Excluded i => i.val
  | .Unbounded => len

/-- [core::slice::{[T]}::copy_within]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 4354:4-4356:16
    Name pattern: [core::slice::{[@T]}::copy_within] -/
@[rust_fun "core::slice::{[@T]}::copy_within"]
def core.slice.Slice.copy_within
  {T : Type} {R : Type} (opsrangeRangeBoundsRUsizeInst :
  core.ops.range.RangeBounds R Std.Usize) (markerCopyInst : core.marker.Copy T)
  :
  Slice T → R → Std.Usize → Result (Slice T) :=
  fun self src dest => do
    let sb ← opsrangeRangeBoundsRUsizeInst.start_bound src
    let eb ← opsrangeRangeBoundsRUsizeInst.end_bound src
    let s := Slice.copyWithinStart sb
    let e := Slice.copyWithinEnd eb self.length
    -- Rust panics if the source range is invalid or the copy runs past the end.
    if s ≤ e ∧ e ≤ self.length ∧ dest.val + (e - s) ≤ self.length then
      ok (self.setSlice! dest.val ((self.val.drop s).take (e - s)))
    else
      fail .panic

/-- **Spec theorem for `<[T]>::copy_within`**: the source range is resolved through
the `RangeBounds` instance, then the segment `self[s, e)` is copied to start at
`dest` (via `Slice.setSlice!`). The bound resolution is definitional in the instance,
so this is stated as an unfolding lemma. -/
@[simp]
theorem core.slice.Slice.copy_within_eq
    {T R : Type} (rbInst : core.ops.range.RangeBounds R Std.Usize)
    (copyInst : core.marker.Copy T) (self : Slice T) (src : R) (dest : Std.Usize) :
    core.slice.Slice.copy_within rbInst copyInst self src dest =
      (do
        let sb ← rbInst.start_bound src
        let eb ← rbInst.end_bound src
        let s := Slice.copyWithinStart sb
        let e := Slice.copyWithinEnd eb self.length
        if s ≤ e ∧ e ≤ self.length ∧ dest.val + (e - s) ≤ self.length then
          ok (self.setSlice! dest.val ((self.val.drop s).take (e - s)))
        else fail .panic) := rfl

/-- [alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<T, A>}::len]:
    Source: '/rustc/library/alloc/src/collections/vec_deque/mod.rs', lines 1633:4-1633:30
    Name pattern: [alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<@T, @A>}::len] -/
@[rust_fun
  "alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<@T, @A>}::len"]
def alloc.collections.vec_deque.VecDeque.len
  {T : Type} {A : Type} :
  alloc.collections.vec_deque.VecDeque T A → Result Std.Usize :=
  fun self => ok self.length

/-- Spec: `VecDeque::len` returns `self.length`. -/
@[step]
theorem alloc.collections.vec_deque.VecDeque.len_spec
    {T : Type} {A : Type} (self : alloc.collections.vec_deque.VecDeque T A) :
    alloc.collections.vec_deque.VecDeque.len self
      ⦃ (n : Std.Usize) => n = self.length ⦄ := by
  simp [alloc.collections.vec_deque.VecDeque.len]

/-- [alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<T, A>}::pop_front]:
    Source: '/rustc/library/alloc/src/collections/vec_deque/mod.rs', lines 2064:4-2064:44
    Name pattern: [alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<@T, @A>}::pop_front] -/
@[rust_fun
  "alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<@T, @A>}::pop_front"]
def alloc.collections.vec_deque.VecDeque.pop_front
  {T : Type} {A : Type} :
  alloc.collections.vec_deque.VecDeque T A → Result ((Option T) ×
    (alloc.collections.vec_deque.VecDeque T A)) :=
  fun self =>
    if self.length = 0#usize then
      ok (none, self)
    else
      if hidx : self.head < self.buf.length then
        let elem := self.buf.val[self.head.val]'hidx
        do
          let head' ← self.head + 1#usize
          let len' ← self.length - 1#usize
          ok (some elem, { self with head := head', length := len' })
      else
        fail .panic

/-- `pop_front` on an empty deque returns `(none, self)`.
  `pop_front` on a non-empty deque returns `(some elem, self')`
  where `elem = buf[head]`, `self'.head = head + 1`,
  `self'.length = length - 1`, and `self'.buf` is unchanged.

  Growing-list model: `head` advances linearly (no wrap-around). -/
@[step]
theorem alloc.collections.vec_deque.VecDeque.pop_front_spec_nonempty
    {T : Type} {A : Type} (self : alloc.collections.vec_deque.VecDeque T A)
    (hidx : self.head < self.buf.length):
    alloc.collections.vec_deque.VecDeque.pop_front self ⦃ (res : (Option T) × (alloc.collections.vec_deque.VecDeque T A)) =>
      (self.length = 0#usize → res.1 = none ∧ res.2 = self) ∧
      (self.length ≠ 0#usize →
        res.1 = (self.buf.val[self.head.val]'hidx) ∧
        res.2.head.val = self.head + 1 ∧
        res.2.length = self.length.val - 1 ∧
        res.2.buf = self.buf) ⦄ := by
  unfold alloc.collections.vec_deque.VecDeque.pop_front
  split
  · rename_i hempty
    simp [hempty]
  · rename_i hne
    simp only
    have : self.head + (1#usize).val ≤ Usize.max := by
      have := self.buf.property; scalar_tac
    have : (1#usize).val ≤ self.length := by scalar_tac
    step*

/-- [alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<T, A>}::push_back]:
    Source: '/rustc/library/alloc/src/collections/vec_deque/mod.rs', lines 2205:4-2205:41
    Name pattern: [alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<@T, @A>}::push_back]

    Growing-list model: appends `value` to the physical buffer and
    increments `length`. The buffer grows on every call (no fixed-capacity
    ring); this is observationally equivalent to Rust's `push_back` at
    the value level and consistent with the capacity-free `Vec` model
    used elsewhere in this codebase. -/
@[rust_fun
  "alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<@T, @A>}::push_back"]
def alloc.collections.vec_deque.VecDeque.push_back
  {T : Type} {A : Type} :
  alloc.collections.vec_deque.VecDeque T A → T → Result
    (alloc.collections.vec_deque.VecDeque T A) :=
  fun self value =>
    if h : self.buf.val.length + 1 ≤ Usize.max then
      do
        let len' ← self.length + 1#usize
        ok { self with
          buf := alloc.vec.Vec.from (self.buf.val ++ [value]) (by simp [List.length_append]; omega)
          length := len' }
    else
      fail .panic

/-- Spec: `push_back` appends `value` to the physical buffer, keeps `head`
    unchanged, and increments `length` by one.

    Growing-list model: no capacity wraparound. -/
@[step]
theorem alloc.collections.vec_deque.VecDeque.push_back_spec
    {T : Type} {A : Type} (self : alloc.collections.vec_deque.VecDeque T A)
    (value : T)
    (hlen : self.length + 1 ≤ Usize.max)
    (hbuf : self.buf.length + 1 ≤ Usize.max) :
    alloc.collections.vec_deque.VecDeque.push_back self value ⦃ (self' : alloc.collections.vec_deque.VecDeque T A) =>
      self'.buf = self.buf ++ [value] ∧
      self'.head = self.head ∧
      self'.length = self.length.val + 1 ⦄ := by
  unfold alloc.collections.vec_deque.VecDeque.push_back
  simp only [dite_eq_left hbuf]
  step*

/-- [alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<T, alloc::alloc::Global>}::new]:
    Source: '/rustc/library/alloc/src/collections/vec_deque/mod.rs'
    Name pattern: [alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<@T, alloc::alloc::Global>}::new]

    Growing-list model: the empty deque (empty buffer, `head = 0`, `length = 0`). -/
@[rust_fun
  "alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<@T, alloc::alloc::Global>}::new"]
def alloc.collections.vec_deque.VecDequeTGlobal.new
  (T : Type) : Result (alloc.collections.vec_deque.VecDeque T Global) :=
  ok { buf := alloc.vec.Vec.new T, head := 0#usize, length := 0#usize }

/-- Spec: `new` returns the empty deque. -/
@[step]
theorem alloc.collections.vec_deque.VecDequeTGlobal.new_spec (T : Type) :
    alloc.collections.vec_deque.VecDequeTGlobal.new T ⦃
      (d : alloc.collections.vec_deque.VecDeque T Global) =>
      d.buf.val = [] ∧ d.head = 0#usize ∧ d.length = 0#usize ⦄ := by
  simp [alloc.collections.vec_deque.VecDequeTGlobal.new, alloc.vec.Vec.new, WP.spec_ok]

/-- [core::hint::must_use]:
    Source: '/rustc/library/core/src/hint.rs', lines 613:0-613:39
    Name pattern: [core::hint::must_use]

    The identity function (it only carries the `#[must_use]` lint). -/
@[rust_fun "core::hint::must_use"]
def core.hint.must_use {T : Type} (value : T) : Result T := ok value

/-- [alloc::fmt::format]:
    Source: '/rustc/library/alloc/src/fmt.rs', lines 651:0-651:52
    Name pattern: [alloc::fmt::format]

    Opaque: the formatted `String` (used only for error messages in spqr). No spec is assumed. -/
@[rust_fun "alloc::fmt::format"]
noncomputable opaque alloc.fmt.format : core.fmt.Arguments → Result String

/-- **Trusted spec axiom for `alloc::fmt::format`**: formatting into a `String` always
succeeds. The resulting string is left unspecified (the model of `alloc.fmt.format` is opaque);
spqr only uses it to build error messages. -/
@[step]
axiom alloc.fmt.format_spec (args : core.fmt.Arguments) :
    alloc.fmt.format args ⦃ (_ : String) => True ⦄

/-- [alloc::string::{impl core::fmt::Debug for alloc::string::String}::fmt]:
    Source: '/rustc/library/alloc/src/string.rs', lines 2793:4-2793:60
    Name pattern: [alloc::string::{core::fmt::Debug<alloc::string::String>}::fmt]

    Opaque: debug formatting (only reached through `expect` on a `Result<_, String>`). No spec
    is assumed. -/
@[rust_fun "alloc::string::{core::fmt::Debug<alloc::string::String>}::fmt"]
noncomputable opaque alloc.string.String.Insts.CoreFmtDebug.fmt :
  String → core.fmt.Formatter → Result ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [alloc::collections::vec_deque::{core::ops::index::IndexMut<usize, T> for alloc::collections::vec_deque::VecDeque<T, A>}::index_mut]:
    Source: '/rustc/library/alloc/src/collections/vec_deque/mod.rs', lines 3634:4-3634:51
    Name pattern: [alloc::collections::vec_deque::{core::ops::index::IndexMut<alloc::collections::vec_deque::VecDeque<@T, @A>, usize, @T>}::index_mut]

    Growing-list model: physical position is `head + idx` (no modular
    wrap-around), consistent with the growing-buffer `push_back` and
    linear-advance `pop_front`. -/
@[rust_fun
  "alloc::collections::vec_deque::{core::ops::index::IndexMut<alloc::collections::vec_deque::VecDeque<@T, @A>, usize, @T>}::index_mut"]
def
  alloc.collections.vec_deque.VecDeque.Insts.CoreOpsIndexIndexMutUsizeT.index_mut
  {T : Type} {A : Type} :
  alloc.collections.vec_deque.VecDeque T A → Std.Usize → Result (T × (T
    → alloc.collections.vec_deque.VecDeque T A)) :=
  fun self idx =>
    if idx.val < self.length then
      if hphys : self.head + idx.val < self.buf.length then
        let elem := self.buf[self.head.val + idx]'hphys
        ok (elem, fun new_elem =>
          { self with buf := alloc.vec.Vec.from (self.buf.val.set (self.head.val + idx) new_elem) (by
              have := self.buf.property
              simp only [List.length_set]; omega) })
      else
        fail .panic
    else
      fail .panic

/-- Spec: `index_mut` (in-bounds) returns `(elem, back)` where
    `elem = buf[head + idx]` and `back x` updates that position to
    `x`, keeping `head` and `length` unchanged.

    Growing-list model: physical position is `head + idx` (linear, no
    modular wrap-around). -/
@[step]
theorem alloc.collections.vec_deque.VecDeque.Insts.CoreOpsIndexIndexMutUsizeT.index_mut_spec
    {T : Type} {A : Type} (self : alloc.collections.vec_deque.VecDeque T A)
    (idx : Std.Usize)
    (hidx : idx.val < self.length)
    (hphys : self.head + idx < self.buf.length) :
    alloc.collections.vec_deque.VecDeque.Insts.CoreOpsIndexIndexMutUsizeT.index_mut
      self idx ⦃ (res : T × (T → alloc.collections.vec_deque.VecDeque T A)) =>
      let phys := self.head + idx.val
      match self.buf.val[phys]? with
        | some elem =>
          res.1 = elem ∧
          ∀ x, (res.2 x).buf = self.buf.val.set phys x ∧
               (res.2 x).head = self.head ∧
               (res.2 x).length = self.length
        | none => False ⦄ := by
  unfold alloc.collections.vec_deque.VecDeque.Insts.CoreOpsIndexIndexMutUsizeT.index_mut
  simp only [ite_eq_left hidx, dite_eq_left hphys]
  simp only [List.getElem?_eq_getElem hphys, WP.spec_ok]
  simp

/-- Models Rust's `<T>::IS_ZST` associated constant; we default to `false`
    since our model does not distinguish zero-sized types. -/
def alloc.collections.vec_deque.IS_ZST (_T : Type) : Bool := false

/-- [alloc::collections::vec_deque::{core::convert::From<[T; N]> for alloc::collections::vec_deque::VecDeque<T, alloc::alloc::Global>}::from]:
    Source: '/rustc/library/alloc/src/collections/vec_deque/mod.rs', lines 3812:4-3812:32
    Name pattern: [alloc::collections::vec_deque::{core::convert::From<alloc::collections::vec_deque::VecDeque<@T, alloc::alloc::Global>, [@T; @N]>}::from] -/
@[rust_fun
  "alloc::collections::vec_deque::{core::convert::From<alloc::collections::vec_deque::VecDeque<@T, alloc::alloc::Global>, [@T; @N]>}::from"]
def
  alloc.collections.vec_deque.VecDequeTGlobal.Insts.CoreConvertFromArray.from
  {T : Type} {N : Std.Usize} :
  Array T N → Result (alloc.collections.vec_deque.VecDeque T Global) :=
  fun arr =>
    -- `let mut deq = VecDeque::with_capacity(N);`
    let deq : alloc.collections.vec_deque.VecDeque T Global :=
      { buf := alloc.vec.Vec.new T, head := 0#usize, length := 0#usize }
    -- `if !<T>::IS_ZST { ptr::copy_nonoverlapping(arr.as_ptr(), deq.ptr(), N); }`
    let deq : alloc.collections.vec_deque.VecDeque T Global :=
      if alloc.collections.vec_deque.IS_ZST T then
        deq
      else
        { deq with buf := alloc.vec.Vec.from arr.val (by have := arr.property; scalar_tac) }
    -- `deq.head = 0; deq.len = N;`
    ok { deq with head := 0#usize, length := N }

/-- Spec: `From<[T;N]>::from` returns a deque with `buf.val = arr.val`,
    `head = 0`, and `length = N`. -/
@[step]
theorem alloc.collections.vec_deque.VecDequeTGlobal.Insts.CoreConvertFromArray.from_spec
    {T : Type} {N : Std.Usize} (arr : Array T N) :
    alloc.collections.vec_deque.VecDequeTGlobal.Insts.CoreConvertFromArray.from arr ⦃ (vd : alloc.collections.vec_deque.VecDeque T Global) =>
      vd.buf.val = arr.val ∧ vd.head = 0#usize ∧ vd.length = N ⦄ := by
  simp [alloc.collections.vec_deque.VecDequeTGlobal.Insts.CoreConvertFromArray.from,
    alloc.collections.vec_deque.IS_ZST]


/-- [alloc::slice::{[T]}::concat]:
    Source: '/rustc/library/alloc/src/slice.rs', lines 578:4-580:27
    Name pattern: [alloc::slice::{[@T]}::concat] -/
@[rust_fun "alloc::slice::{[@T]}::concat"]
def alloc.slice.Slice.concat
  {T : Type} {Item : Type} {Clause0_Output : Type}
  (ConcatSliceItemClause0_OutputInst : alloc.slice.Concat (Slice T) Item
  Clause0_Output) :
  Slice T → Result Clause0_Output :=
  fun s => ConcatSliceItemClause0_OutputInst.concat s

/-- **Spec theorem for `<[T]>::concat`**: the free function delegates to the
`Concat` trait instance. -/
@[simp]
theorem alloc.slice.Slice.concat_eq
    {T Item Clause0_Output : Type}
    (inst : alloc.slice.Concat (Slice T) Item Clause0_Output) (s : Slice T) :
    alloc.slice.Slice.concat inst s = inst.concat s := rfl

/-- Implementation helper for `Slice.Insts.AllocSliceConcatTVec.concat`
(`[alloc::slice::{alloc::slice::Concat<[@V], @T, alloc::vec::Vec<@T>>}::concat]`,
Source: '/rustc/library/alloc/src/slice.rs', lines 730:4-730:37).

Package an element list as a `Vec`, failing if it would exceed `Usize.max`. -/
def Slice.listToVec {T : Type} (l : List T) : Result (alloc.vec.Vec T) :=
  if h : l.length ≤ Std.Usize.max then ok (alloc.vec.Vec.from l h) else fail .panic

/-- Implementation helper for `Slice.Insts.AllocSliceConcatTVec.concat`
(`[alloc::slice::{alloc::slice::Concat<[@V], @T, alloc::vec::Vec<@T>>}::concat]`,
Source: '/rustc/library/alloc/src/slice.rs', lines 730:4-730:37).

Flatten a list of borrowable chunks: borrow each `V` to a `Slice T`, clone its
elements, and concatenate the results into one element list. -/
def Slice.concatListAux {T V : Type} (corecloneCloneInst : core.clone.Clone T)
    (coreborrowBorrowVSliceInst : core.borrow.Borrow V (Slice T)) :
    List V → Result (List T)
  | [] => ok []
  | v :: vs => do
    let s ← coreborrowBorrowVSliceInst.borrow v
    let cs ← Slice.clone corecloneCloneInst.clone s
    let rest ← Slice.concatListAux corecloneCloneInst coreborrowBorrowVSliceInst vs
    ok (cs.val ++ rest)

/-- [alloc::slice::{alloc::slice::Concat<T, alloc::vec::Vec<T>> for [V]}::concat]:
    Source: '/rustc/library/alloc/src/slice.rs', lines 730:4-730:37
    Name pattern: [alloc::slice::{alloc::slice::Concat<[@V], @T, alloc::vec::Vec<@T>>}::concat] -/
@[rust_fun
  "alloc::slice::{alloc::slice::Concat<[@V], @T, alloc::vec::Vec<@T>>}::concat"]
def Slice.Insts.AllocSliceConcatTVec.concat
  {T : Type} {V : Type} (corecloneCloneInst : core.clone.Clone T)
  (coreborrowBorrowVSliceInst : core.borrow.Borrow V (Slice T)) :
  Slice V → Result (alloc.vec.Vec T) :=
  fun sv => do
    let l ← Slice.concatListAux corecloneCloneInst coreborrowBorrowVSliceInst sv.val
    Slice.listToVec l

/-- **Spec theorem for `Concat<[V], T, Vec<T>>::concat`**: the result is the
flattening produced by `Slice.concatListAux`, packaged as a `Vec`. The chunk
contents are definitional in the `Borrow`/`Clone` instances. -/
@[simp]
theorem Slice.Insts.AllocSliceConcatTVec.concat_eq
    {T V : Type} (corecloneCloneInst : core.clone.Clone T)
    (coreborrowBorrowVSliceInst : core.borrow.Borrow V (Slice T)) (sv : Slice V) :
    Slice.Insts.AllocSliceConcatTVec.concat corecloneCloneInst
        coreborrowBorrowVSliceInst sv =
      (do
        let l ← Slice.concatListAux corecloneCloneInst coreborrowBorrowVSliceInst sv.val
        Slice.listToVec l) := rfl

/-- **Spec theorem for `Concat<[V], T, Vec<T>>::concat` with shared borrow and identity clone**:
concatenating a slice of slices yields a `Vec` whose underlying list is the flattened
concatenation, provided `Clone` is the identity (`hclone`) and the total length fits
in `Usize` (`hlen`). -/
theorem Slice.Insts.AllocSliceConcatTVec.concat_shared_id_spec
    {T : Type} (corecloneCloneInst : core.clone.Clone T)
    (hclone : ∀ x, corecloneCloneInst.clone x = ok x)
    (sv : Slice (Slice T))
    (hlen : (sv.val.map (·.val)).flatten.length ≤ Std.Usize.max) :
    Slice.Insts.AllocSliceConcatTVec.concat corecloneCloneInst
        { borrow := Shared0T.Insts.CoreBorrowBorrow.borrow } sv ⦃ (v : alloc.vec.Vec T) =>
      v.val = (sv.val.map (·.val)).flatten ⦄ := by
  set b : core.borrow.Borrow (Slice T) (Slice T) :=
    { borrow := Shared0T.Insts.CoreBorrowBorrow.borrow }
  have h : ∀ l, Slice.concatListAux corecloneCloneInst b l ⦃ r =>
      r = (l.map (·.val)).flatten ⦄ := by
    intro l
    induction l with
    | nil => simp [Slice.concatListAux]
    | cons hd tl ih =>
      simp only [Slice.concatListAux, Shared0T.Insts.CoreBorrowBorrow.borrow, b, bind_ok]
      step with Slice.clone_spec (s := hd) fun _ _ => hclone _ as ⟨cs, h_cs⟩
      step with ih as ⟨rest, h_rest⟩
      simp [h_cs, h_rest]
  simp only [Slice.Insts.AllocSliceConcatTVec.concat_eq]
  step with h sv.val as ⟨l, h_l⟩
  unfold Slice.listToVec
  rw [dite_eq_left (h_l ▸ hlen)]
  simp only [WP.spec_ok, alloc.vec.Vec.from_val, h_l]

/-- [alloc::str::{alloc::borrow::ToOwned<alloc::string::String> for str}::to_owned]:
    Source: '/rustc/library/alloc/src/str.rs', lines 210:4-210:32
    Name pattern: [alloc::str::{alloc::borrow::ToOwned<str, alloc::string::String>}::to_owned]

    In Rust, `str::to_owned` copies the bytes of a `&str` into a freshly allocated `String`
    (`String::from_utf8_unchecked(self.as_bytes().to_owned())`). It never fails: its only
    failure mode is allocation failure, which aborts the process instead of returning. We model
    it by decoding the slice's bytes as UTF-8 (a Lean `String` is a `ByteArray` of valid UTF-8
    bytes plus the validity proof); the `fail` branch is unreachable on any `Str` produced by
    `toStr`, in particular on the string literals appearing in the extracted code. -/
@[rust_fun
  "alloc::str::{alloc::borrow::ToOwned<str, alloc::string::String>}::to_owned"]
def Str.Insts.AllocBorrowToOwnedString.to_owned : Str → Result String :=
  fun s =>
    let bytes : ByteArray := ⟨⟨s.val.map (fun b => UInt8.ofNat b.val)⟩⟩
    if h : bytes.IsValidUTF8 then ok ⟨bytes, h⟩ else fail .panic

/-- `ByteArray.toList` agrees with the underlying array's `toList`. -/
theorem ByteArray.toList_eq_data_toList (bs : ByteArray) :
    bs.toList = bs.data.toList := by
  obtain ⟨data⟩ := bs
  have loop_eq : ∀ (i : Nat) (r : List UInt8), i ≤ data.size →
      ByteArray.toList.loop ⟨data⟩ i r = r.reverse ++ data.toList.drop i := by
    intro i r hi
    fun_induction ByteArray.toList.loop ⟨data⟩ i r with
    | case1 i r h ih =>
      have hlen : i < data.toList.length := h
      rw [ih (Nat.succ_le_of_lt h), List.drop_eq_getElem_cons (i := i) (l := data.toList) hlen,
        List.reverse_cons, List.append_assoc, List.singleton_append]
      simp only [ByteArray.get!]
      rw [getElem!_pos, Array.getElem_toList]
    | case2 i r h =>
      rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt h), List.append_nil]
  unfold ByteArray.toList
  rw [loop_eq 0 [] (Nat.zero_le _), List.drop_zero, List.reverse_nil, List.nil_append]

/-- **Spec theorem for `str::to_owned`**: on a string slice built from a Lean `String` by
`toStr`, the call always succeeds and the resulting owned `String` has the same contents. -/
@[step]
theorem Str.Insts.AllocBorrowToOwnedString.to_owned_spec (s : String)
    (h : s.toByteArray.size ≤ U32.max) :
    Str.Insts.AllocBorrowToOwnedString.to_owned (toStr s h) ⦃ (result : String) =>
      result = s ⦄ := by
  have hbytes :
      (⟨⟨(toStr s h).val.map (fun b => UInt8.ofNat b.val)⟩⟩ : ByteArray) = s.toByteArray := by
    simp only [toStr, Slice.from_val, List.map_map, Function.comp_def, UScalar.val,
      BitVec.toNat_ofFin, UInt8.ofNat_toNat, List.map_id', ByteArray.toList_eq_data_toList]
  simp only [Str.Insts.AllocBorrowToOwnedString.to_owned, hbytes, s.isValidUTF8, dite_eq_left]
  step*

/-- [alloc::vec::{alloc::vec::Vec<T>}::truncate]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 1696:4-1696:42
    Name pattern: [alloc::vec::{alloc::vec::Vec<@T>}::truncate] -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::truncate"]
def alloc.vec.Vec.truncate
  {T : Type} (A : Type) :
  alloc.vec.Vec T → Std.Usize → Result (alloc.vec.Vec T) :=
  fun v n => ok (alloc.vec.Vec.from (v.val.take n.val) (by
    have := v.property; simp only [List.length_take]; omega))

/-- **Spec theorem for `Vec::truncate`**: keeps the first `n` elements. -/
@[step]
theorem alloc.vec.Vec.truncate_spec
    {T : Type} (A : Type) (v : alloc.vec.Vec T) (n : Std.Usize) :
    alloc.vec.Vec.truncate A v n ⦃ nv => nv.val = v.val.take n.val ⦄ := by
  simp [alloc.vec.Vec.truncate]

/-- [alloc::vec::{alloc::vec::Vec<T>}::as_slice]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 1733:4-1733:40
    Name pattern: [alloc::vec::{alloc::vec::Vec<@T>}::as_slice] -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::as_slice"]
def alloc.vec.Vec.as_slice
  {T : Type} (A : Type) : alloc.vec.Vec T → Result (Slice T) :=
  fun v => ok (Slice.from v.val v.property)

/-- **Spec theorem for `Vec::as_slice`**: the slice view shares the vector's
elements. -/
@[step]
theorem alloc.vec.Vec.as_slice_spec
    {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    alloc.vec.Vec.as_slice A v ⦃ s => s.val = v.val ⦄ := by
  simp [alloc.vec.Vec.as_slice]

/-- [alloc::vec::{alloc::vec::Vec<T>}::remove]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 2276:4-2276:47
    Name pattern: [alloc::vec::{alloc::vec::Vec<@T>}::remove] -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::remove"]
def alloc.vec.Vec.remove
  {T : Type} (A : Type) :
  alloc.vec.Vec T → Std.Usize → Result (T × (alloc.vec.Vec T)) :=
  fun v i =>
    if h : i.val < v.val.length then
      ok (v.val[i.val]'h, alloc.vec.Vec.from (v.val.eraseIdx i.val) (by
        have := v.property; have := List.length_eraseIdx_le v.val i.val; omega))
    else
      fail .arrayOutOfBounds

/-- **Spec theorem for `Vec::remove`**: removes (and returns) the element at index
`i`, shifting the remaining elements left. Panics (here: fails) when out of bounds. -/
@[step]
theorem alloc.vec.Vec.remove_spec
    {T : Type} (A : Type) (v : alloc.vec.Vec T) (i : Std.Usize)
    (hbound : i.val < v.val.length) :
    alloc.vec.Vec.remove A v i ⦃ (x, nv) =>
      x = v.val[i.val] ∧ nv.val = v.val.eraseIdx i.val ⦄ := by
  simp [alloc.vec.Vec.remove, hbound]

/-- [alloc::vec::{alloc::vec::Vec<T>}::append]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 2802:4-2802:46
    Name pattern: [alloc::vec::{alloc::vec::Vec<@T>}::append] -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::append"]
def alloc.vec.Vec.append
  {T : Type} (A : Type) :
  alloc.vec.Vec T → alloc.vec.Vec T → Result ((alloc.vec.Vec T) ×
    (alloc.vec.Vec T)) :=
  fun v1 v2 =>
    if h : v1.val.length + v2.val.length ≤ Std.Usize.max then
      ok (alloc.vec.Vec.from (v1.val ++ v2.val) (by simp only [List.length_append]; omega),
          alloc.vec.Vec.new T)
    else
      fail .panic

/-- **Spec theorem for `Vec::append`**: drains all of `v2` onto the end of `v1`;
following Aeneas's mutable-reference convention it returns both the extended `v1`
and the now-empty `v2`. -/
@[step]
theorem alloc.vec.Vec.append_spec
    {T : Type} (A : Type) (v1 v2 : alloc.vec.Vec T)
    (h : v1.val.length + v2.val.length ≤ Std.Usize.max) :
    alloc.vec.Vec.append A v1 v2 ⦃ (r1, r2) =>
      r1.val = v1.val ++ v2.val ∧ r2.val = [] ⦄ := by
  simp [alloc.vec.Vec.append, h, alloc.vec.Vec.new]

/-- [alloc::vec::{alloc::vec::Vec<T>}::clear]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 2903:4-2903:27
    Name pattern: [alloc::vec::{alloc::vec::Vec<@T>}::clear] -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::clear"]
def alloc.vec.Vec.clear
  {T : Type} (A : Type) : alloc.vec.Vec T → Result (alloc.vec.Vec T) :=
  fun _ => ok (alloc.vec.Vec.new T)

/-- **Spec theorem for `Vec::clear`**: empties the vector. -/
@[step]
theorem alloc.vec.Vec.clear_spec
    {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    alloc.vec.Vec.clear A v ⦃ nv => nv.val = [] ⦄ := by
  simp [alloc.vec.Vec.clear, alloc.vec.Vec.new]

/-- [alloc::vec::{alloc::vec::Vec<T>}::is_empty]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 2956:4-2956:40
    Name pattern: [alloc::vec::{alloc::vec::Vec<@T>}::is_empty] -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::is_empty"]
def alloc.vec.Vec.is_empty
  {T : Type} (A : Type) : alloc.vec.Vec T → Result Bool :=
  fun v => ok v.val.isEmpty

/-- **Spec theorem for `Vec::is_empty`**: `true` iff the underlying list is empty. -/
@[step]
theorem alloc.vec.Vec.is_empty_spec
    {T : Type} (A : Type) (v : alloc.vec.Vec T) :
    alloc.vec.Vec.is_empty A v ⦃ b => b = v.val.isEmpty ⦄ := by
  simp [alloc.vec.Vec.is_empty]

/-- [alloc::vec::{alloc::vec::Vec<T>}::split_off]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 2989:4-2991:17
    Name pattern: [alloc::vec::{alloc::vec::Vec<@T>}::split_off] -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::split_off"]
def alloc.vec.Vec.split_off
  {T : Type} {A : Type} (corecloneCloneInst : core.clone.Clone A) :
  alloc.vec.Vec T → Std.Usize → Result ((alloc.vec.Vec T) × (alloc.vec.Vec
    T)) :=
  fun v at_ =>
    if h : at_.val ≤ v.val.length then
      -- Aeneas `&mut self` convention: `(return_value, updated_self)`.
      -- `split_off` returns the suffix `[at_, len)` and leaves `self = [0, at_)`.
      ok (alloc.vec.Vec.from (v.val.drop at_.val) (by
            have := v.property; simp only [List.length_drop]; omega),
          alloc.vec.Vec.from (v.val.take at_.val) (by
            have := v.property; simp only [List.length_take]; omega))
    else
      fail .panic

/-- **Spec theorem for `Vec::split_off`**: splits at index `at_`. Following Aeneas's
mutable-reference convention `(return_value, updated_self)`, the first component is
the returned suffix `[at_, len)` and the second is the truncated `self` `[0, at_)`.
Panics (here: fails) when `at_` exceeds the length. -/
@[step]
theorem alloc.vec.Vec.split_off_spec
    {T A : Type} (corecloneCloneInst : core.clone.Clone A)
    (v : alloc.vec.Vec T) (at_ : Std.Usize) (hbound : at_.val ≤ v.val.length) :
    alloc.vec.Vec.split_off corecloneCloneInst v at_ ⦃ (r1, r2) =>
      r1.val = v.val.drop at_.val ∧ r2.val = v.val.take at_.val ⦄ := by
  simp [alloc.vec.Vec.split_off, hbound]

/-- [alloc::vec::{core::default::Default for alloc::vec::Vec<T>}::default]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 4171:4-4171:26
    Name pattern: [alloc::vec::{core::default::Default<alloc::vec::Vec<@T>>}::default] -/
@[rust_fun
  "alloc::vec::{core::default::Default<alloc::vec::Vec<@T>>}::default"]
def alloc.vec.Vec.Insts.CoreDefaultDefault.default
  (T : Type) : Result (alloc.vec.Vec T) :=
  ok (alloc.vec.Vec.new T)

/-- **Spec theorem for `Default for Vec<T>`**: the default vector is empty. -/
@[step]
theorem alloc.vec.Vec.Insts.CoreDefaultDefault.default_spec (T : Type) :
    alloc.vec.Vec.Insts.CoreDefaultDefault.default T ⦃ v => v.val = [] ⦄ := by
  simp [alloc.vec.Vec.Insts.CoreDefaultDefault.default, alloc.vec.Vec.new]

/-- [libcrux_hmac::hmac]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/libcrux-hmac-0.0.6/src/hmac.rs', lines 51:0-51:90
    Name pattern: [libcrux_hmac::hmac] -/
@[rust_fun "libcrux_hmac::hmac"]
noncomputable opaque libcrux_hmac.hmac
  :
  libcrux_hmac.Algorithm → Slice Std.U8 → Slice Std.U8 → Option Std.Usize
    → Result (alloc.vec.Vec Std.U8)

/-- **Axiom claim:** If `key.length ≤ u32::MAX` and `data.length ≤ u32::MAX`, then
`libcrux_hmac::hmac(Sha256, key, data, Some(32))` is panic-free and returns an
`alloc::vec::Vec<u8>` of length exactly `32`.

**External source references (libcrux-hmac 0.0.6):**

* wrapper, `src/hmac.rs`:
  <https://docs.rs/libcrux-hmac/0.0.6/src/libcrux_hmac/hmac.rs.html>

* glue, `src/impl_hacl.rs`:
  <https://docs.rs/libcrux-hmac/0.0.6/src/libcrux_hmac/impl_hacl.rs.html>

This axiom is designed to maximise three desiderata simultaneously:

**(a) Sufficiency for downstream specs:** This axiom allows to formulate and
prove spec theorems for `mac_ct` and `mac_hdr`, which in turn unblock a variety
of dependent spec theorems.

**(b) Faithfulness to the external sources:** Both halves of the claim follow
from inspecting the external source references:

  * *Panic-freedom (no panic under the given settings).* The only potential
    panic sites sit in the glue layer `src/impl_hacl.rs`, namely the two
    `usize → u32` casts `key.len().try_into().unwrap()` and
    `data.len().try_into().unwrap()`. The hypotheses
    `key.length ≤ u32::MAX` and `data.length ≤ u32::MAX` ensure that neither
    `try_into` returns `Err`, so the two `unwrap()` calls (and hence the
    whole call) cannot panic.

  * *Output length is `32` (under the given settings).* For
    `Algorithm.Sha256`, the wrapper calls `wrap_bufalloc(|buf| hmac_sha2_256(buf, …))`,
    which allocates a stack buffer `[u8; 32]`, lets `hmac_sha2_256` fill it
    through the `&mut [u8; 32]` parameter, and returns it as `buf.to_vec()`, which is
    a `Vec<u8>` of length `32`. The wrapper then calls `dst.truncate(32)`.
    Since `Vec::truncate(n)` is a no-op when the vector already has length
    `≤ n`, the returned vector has length exactly `32`.

**(c) Minimality of trust base extension:** Both call sites of `libcrux_hmac.hmac`
in `Funs.lean` use precisely `Algorithm.Sha256` and `some MACSIZE` with
`MACSIZE = 32`, so the axiom is specialised to exactly the shape that occurs
in this codebase and adds no surplus assumptions. -/
@[step]
axiom libcrux_hmac.hmac_sha256_tag32_spec
    (key data : Slice U8)
    (hkey : key.length ≤ U32.max)
    (hdata : data.length ≤ U32.max) :
    libcrux_hmac.hmac .Sha256 key data (some 32#usize)
      ⦃ (r : alloc.vec.Vec U8) => r.length = 32 ⦄

/-- [libcrux_ml_kem::constants::SHARED_SECRET_SIZE]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/libcrux-ml-kem-0.0.7/src/constants.rs', lines 14:0-14:35
    Name pattern: [libcrux_ml_kem::constants::SHARED_SECRET_SIZE] -/
@[rust_const "libcrux_ml_kem::constants::SHARED_SECRET_SIZE"]
def libcrux_ml_kem.constants.SHARED_SECRET_SIZE : Result Std.Usize :=
  -- `pub const SHARED_SECRET_SIZE: usize = 32;`
  ok 32#usize

/-- **Spec theorem for `libcrux_ml_kem::constants::SHARED_SECRET_SIZE`**: the constant is `32`. -/
@[step]
theorem libcrux_ml_kem.constants.SHARED_SECRET_SIZE_spec :
    libcrux_ml_kem.constants.SHARED_SECRET_SIZE ⦃ (r : Std.Usize) => r.val = 32 ⦄ := by
  simp only [libcrux_ml_kem.constants.SHARED_SECRET_SIZE, WP.spec_ok]
  rfl

/-- [libcrux_ml_kem::ind_cca::incremental::types::{core::fmt::Debug for libcrux_ml_kem::ind_cca::incremental::types::Error}::fmt]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/libcrux-ml-kem-0.0.7/src/ind_cca/incremental/types.rs', lines 13:9-13:14
    Name pattern: [libcrux_ml_kem::ind_cca::incremental::types::{core::fmt::Debug<libcrux_ml_kem::ind_cca::incremental::types::Error>}::fmt] -/
@[rust_fun
  "libcrux_ml_kem::ind_cca::incremental::types::{core::fmt::Debug<libcrux_ml_kem::ind_cca::incremental::types::Error>}::fmt"]
noncomputable opaque libcrux_ml_kem.ind_cca.incremental.types.Error.Insts.CoreFmtDebug.fmt
  :
  libcrux_ml_kem.ind_cca.incremental.types.Error → core.fmt.Formatter →
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [libcrux_ml_kem::ind_cca::incremental::types::{libcrux_ml_kem::ind_cca::incremental::types::Ciphertext1<LEN>}::len]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/libcrux-ml-kem-0.0.7/src/ind_cca/incremental/types.rs', lines 161:4-161:31
    Name pattern: [libcrux_ml_kem::ind_cca::incremental::types::{libcrux_ml_kem::ind_cca::incremental::types::Ciphertext1<@LEN>}::len] -/
@[rust_fun
  "libcrux_ml_kem::ind_cca::incremental::types::{libcrux_ml_kem::ind_cca::incremental::types::Ciphertext1<@LEN>}::len"]
noncomputable opaque libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1.len
  (LEN : Std.Usize) : Result Std.Usize

/-- [libcrux_ml_kem::ind_cca::incremental::types::{libcrux_ml_kem::ind_cca::incremental::types::Ciphertext2<LEN>}::len]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/libcrux-ml-kem-0.0.7/src/ind_cca/incremental/types.rs', lines 174:4-174:31
    Name pattern: [libcrux_ml_kem::ind_cca::incremental::types::{libcrux_ml_kem::ind_cca::incremental::types::Ciphertext2<@LEN>}::len] -/
@[rust_fun
  "libcrux_ml_kem::ind_cca::incremental::types::{libcrux_ml_kem::ind_cca::incremental::types::Ciphertext2<@LEN>}::len"]
noncomputable opaque libcrux_ml_kem.ind_cca.incremental.types.Ciphertext2.len
  (LEN : Std.Usize) : Result Std.Usize

/-- [libcrux_ml_kem::mlkem768::incremental::pk1_len]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/libcrux-ml-kem-0.0.7/src/mlkem.rs', lines 26:8-26:39
    Name pattern: [libcrux_ml_kem::mlkem768::incremental::pk1_len] -/
@[rust_fun "libcrux_ml_kem::mlkem768::incremental::pk1_len"]
noncomputable opaque libcrux_ml_kem.mlkem768.incremental.pk1_len : Result Std.Usize

/-- [libcrux_ml_kem::mlkem768::incremental::pk2_len]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/libcrux-ml-kem-0.0.7/src/mlkem.rs', lines 31:8-31:39
    Name pattern: [libcrux_ml_kem::mlkem768::incremental::pk2_len] -/
@[rust_fun "libcrux_ml_kem::mlkem768::incremental::pk2_len"]
noncomputable opaque libcrux_ml_kem.mlkem768.incremental.pk2_len : Result Std.Usize

/-- [libcrux_ml_kem::mlkem768::incremental::encaps_state_len]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/libcrux-ml-kem-0.0.7/src/mlkem.rs', lines 59:8-59:48
    Name pattern: [libcrux_ml_kem::mlkem768::incremental::encaps_state_len] -/
@[rust_fun "libcrux_ml_kem::mlkem768::incremental::encaps_state_len"]
def libcrux_ml_kem.mlkem768.incremental.encaps_state_len : Result Std.Usize :=
  -- `(RANK + 1) * PolynomialRingElement::num_bytes() + 32 = 4 * 512 + 32 = 2080`
  ok 2080#usize

/-- **Spec theorem for `libcrux_ml_kem::mlkem768::incremental::encaps_state_len`**: the
serialised encapsulation state has `2080` bytes. -/
@[step]
theorem libcrux_ml_kem.mlkem768.incremental.encaps_state_len_spec :
    libcrux_ml_kem.mlkem768.incremental.encaps_state_len ⦃ (r : Std.Usize) =>
      r.val = Fips203.Refinement.encapsStateSize ⦄ := by
  simp only [libcrux_ml_kem.mlkem768.incremental.encaps_state_len, WP.spec_ok]
  rfl

/-- [libcrux_ml_kem::mlkem768::incremental::encapsulate2]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/libcrux-ml-kem-0.0.7/src/mlkem.rs', lines 407:8-407:111
    Name pattern: [libcrux_ml_kem::mlkem768::incremental::encapsulate2] -/
@[rust_fun "libcrux_ml_kem::mlkem768::incremental::encapsulate2"]
noncomputable def libcrux_ml_kem.mlkem768.incremental.encapsulate2
  (state : Array Std.U8 2080#usize) (pk2 : Array Std.U8 1152#usize) :
  Result (libcrux_ml_kem.ind_cca.incremental.types.Ciphertext2 128#usize) :=
  -- Model: round 2 of FIPS 203 `ML-KEM.Encaps_internal` (`Fips203.mlkemEncapsPhase2`): decode the
  -- 2080-byte state `ŷ ‖ e₂ ‖ m` and `t̂` from `pk2 = ByteEncode₁₂(t̂)`, then output
  -- `c₂ = ByteEncode_{d_v}(Compress_{d_v}(NTT⁻¹(t̂ᵀ∘ŷ) + e₂ + Decompress₁(m)))`.  Both inputs are
  -- fixed-size arrays, so there are no error cases and the function never fails.
  -- See `Spqr/Crypto/Fips203/Refinement/EncapsBytes.lean`.
  ok { value := Fips203.Refinement.ct2Array state pk2 }

/-- **Spec theorem for `libcrux_ml_kem::mlkem768::incremental::encapsulate2`**

- Never panics (both inputs are fixed-size arrays, so there are no length checks).
- Returns the `128`-byte second ciphertext half `c₂` of round 2 of FIPS 203 Algorithm 17
  (`Fips203.mlkemEncapsPhase2`) on the state `(ŷ, e₂, m)` decoded from `state` and the
  NTT-domain vector `t̂` decoded from `pk2` (`Fips203.Refinement.ct2List`). -/
@[step]
theorem libcrux_ml_kem.mlkem768.incremental.encapsulate2_spec
    (state : Array Std.U8 2080#usize) (pk2 : Array Std.U8 1152#usize) :
    libcrux_ml_kem.mlkem768.incremental.encapsulate2 state pk2
      ⦃ (r : libcrux_ml_kem.ind_cca.incremental.types.Ciphertext2 128#usize) =>
      r.value.length = 128 ∧ r.value.val = Fips203.Refinement.ct2List state pk2 ⦄ := by
  simp only [libcrux_ml_kem.mlkem768.incremental.encapsulate2, WP.spec_ok]
  exact ⟨Array.length_eq _, rfl⟩

/-- [libcrux_ml_kem::mlkem768::incremental::{libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes}::from_seed]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/libcrux-ml-kem-0.0.7/src/mlkem.rs', lines 240:12-240:80
    Name pattern: [libcrux_ml_kem::mlkem768::incremental::{libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes}::from_seed] -/
@[rust_fun
  "libcrux_ml_kem::mlkem768::incremental::{libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes}::from_seed"]
noncomputable def libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.from_seed
  (seed : Array Std.U8 64#usize) : Result
    libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes :=
  -- Model: FIPS 203 `ML-KEM.KeyGen_internal(d, z)` with `d = seed[0:32]`, `z = seed[32:64]`,
  -- serialised as `dk = dkPKE ‖ ek ‖ H(ek) ‖ z` — byte-for-byte the libcrux layout
  -- (`KeyPair::to_bytes_compressed`).  See `Spqr/Crypto/Fips203/Refinement/KeyPairBytes.lean`.
  ok { value := Fips203.Refinement.keyPairArray (Fips203.Refinement.seedOfArray seed) }

/-- **Spec theorem for `libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes::from_seed`**

- Key generation from a 64-byte seed does not panic.
- The returned buffer has the decapsulation-key length `2400`.
- The buffer is exactly the FIPS 203 (Algorithm 16) decapsulation key
  `ML-KEM.KeyGen_internal(seed[0:32], seed[32:64]).dk` (`Fips203.Refinement.keyPairList`), as libcrux
  lays it out: `ByteEncode₁₂(ŝ) ‖ ByteEncode₁₂(t̂) ‖ ρ ‖ H(ek) ‖ z`. -/
@[step]
theorem libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.from_seed_spec
    (seed : Array Std.U8 64#usize) :
    libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.from_seed seed
      ⦃ (kp : libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes) =>
      kp.value.length = mlkem768Params.decapsulationKeyBytes ∧
      kp.value.val = Fips203.Refinement.keyPairList (Fips203.Refinement.seedOfArray seed) ⦄ := by
  simp only [libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.from_seed, WP.spec_ok]
  exact ⟨Array.length_eq _, rfl⟩

/-- [libcrux_ml_kem::mlkem768::incremental::{libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes}::pk1]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/libcrux-ml-kem-0.0.7/src/mlkem.rs', lines 267:12-267:49
    Name pattern: [libcrux_ml_kem::mlkem768::incremental::{libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes}::pk1] -/
@[rust_fun
  "libcrux_ml_kem::mlkem768::incremental::{libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes}::pk1"]
def libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.pk1
  (k : libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes) :
  Result (Array Std.U8 64#usize) :=
  ok (Array.make 64#usize
    (k.value.val.slice
      (2 * mlkem768Params.encapsulationKeyBytes)
      (2 * mlkem768Params.encapsulationKeyBytes + headerBytes))
    (by
      have h : k.value.val.length = mlkem768Params.decapsulationKeyBytes := Array.length_eq _
      simp only [List.slice_length, headerBytes, seedBytes, mlkem768Params,
        MlkemParams.encapsulationKeyBytes, MlkemParams.serializedPolyBytes,
        MlkemParams.decapsulationKeyBytes] at h ⊢
      scalar_tac))


/-- **Spec theorem for `libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes::pk1`**

- Extracting the header buffer does not panic and returns exactly the header sub-range of the
  shared `value` buffer, i.e. the `64` bytes `value[2·enc .. 2·enc + 64]` (with
  `enc = encapsulationKeyBytes`).
- The second conjunct is the *faithful layout fact*: `pk1` is a byte-for-byte slice of the buffer
  that `sk` returns whole — not merely a buffer of the right size. -/
@[step]
theorem libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.pk1_spec
    (k : libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes) :
    libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.pk1 k
      ⦃ (r : Array Std.U8 64#usize) =>
      r.length = headerBytes ∧
      r.val = k.value.val.slice
        (2 * mlkem768Params.encapsulationKeyBytes)
        (2 * mlkem768Params.encapsulationKeyBytes + headerBytes) ⦄ := by
  simp only [libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.pk1, WP.spec_ok]
  exact ⟨Array.length_eq _, by simp [Array.make_val]⟩

/-- [libcrux_ml_kem::mlkem768::incremental::{libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes}::pk2]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/libcrux-ml-kem-0.0.7/src/mlkem.rs', lines 275:12-275:49
    Name pattern: [libcrux_ml_kem::mlkem768::incremental::{libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes}::pk2] -/
@[rust_fun
  "libcrux_ml_kem::mlkem768::incremental::{libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes}::pk2"]
def libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.pk2
  (k : libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes) :
  Result (Array Std.U8 1152#usize) :=
  ok (Array.make 1152#usize
    (k.value.val.slice
      mlkem768Params.encapsulationKeyBytes
      (2 * mlkem768Params.encapsulationKeyBytes))
    (by
      have h : k.value.val.length = mlkem768Params.decapsulationKeyBytes := Array.length_eq _
      simp only [List.slice_length, seedBytes, mlkem768Params,
        MlkemParams.encapsulationKeyBytes, MlkemParams.serializedPolyBytes,
        MlkemParams.decapsulationKeyBytes] at h ⊢
      scalar_tac))

/-- **Spec theorem for `libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes::pk2`**

- Extracting the encapsulation-key buffer does not panic and returns exactly the sub-range
  of the shared `value` buffer, i.e. the `1152` bytes `value[enc .. 2·enc]` (with
  `enc = encapsulationKeyBytes`).
- `pk2` is a byte-for-byte slice of the buffer that `sk` returns whole — not merely a buffer of the right
size. -/
@[step]
theorem libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.pk2_spec
    (k : libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes) :
    libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.pk2 k
      ⦃ (r : Array Std.U8 1152#usize) =>
      r.length = mlkem768Params.encapsulationKeyBytes ∧
      r.val = k.value.val.slice
        mlkem768Params.encapsulationKeyBytes
        (2 * mlkem768Params.encapsulationKeyBytes) ⦄ := by
  simp only [libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.pk2, WP.spec_ok]
  exact ⟨Array.length_eq _, by simp [Array.make_val]⟩

/-- [libcrux_ml_kem::mlkem768::incremental::{libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes}::sk]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/libcrux-ml-kem-0.0.7/src/mlkem.rs', lines 283:12-283:54
    Name pattern: [libcrux_ml_kem::mlkem768::incremental::{libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes}::sk] -/
@[rust_fun
  "libcrux_ml_kem::mlkem768::incremental::{libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes}::sk"]
def libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.sk
  (k : libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes) :
  Result (Array Std.U8 2400#usize) :=
  -- Rust: `sk(&self) -> &[u8; SECRET_KEY_SIZE] { &self.value }` — the *whole* buffer.
  ok k.value

/-- **Spec theorem for `libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes::sk`**

- Extracting the decapsulation-key buffer does not panic and returns the entire shared
  `value` buffer (whose return type `[u8; 2400]` pins the decapsulation-key size).
- `sk` returns `value` whole while `pk1`/`pk2` are slices of that same `value`, this is the buffer of
which the two public keys are sub-ranges. -/
@[step]
theorem libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.sk_spec
    (k : libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes) :
    libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.sk k
      ⦃ (r : Array Std.U8 2400#usize) =>
      r.length = mlkem768Params.decapsulationKeyBytes ∧ r.val = k.value.val ⦄ := by
  unfold libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.sk
  exact (WP.spec_ok _).mpr ⟨Array.length_eq _, rfl⟩

/-- [libcrux_ml_kem::mlkem768::incremental::validate_pk_bytes]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/libcrux-ml-kem-0.0.7/src/mlkem.rs', lines 333:8-336:30
    Name pattern: [libcrux_ml_kem::mlkem768::incremental::validate_pk_bytes]

    Concrete model of Rust's `validate_pk_bytes(pk1, pk2)`
    (`src/ind_cca/incremental.rs` lines 297–339, `validate_pk_bytes` + `validate_pk_parts`):
    1. Length check: fails with `InvalidInputLength` unless `pk1.len() == 64` **and**
       `pk2.len() == 1152` (exact equality; over-long inputs are rejected).
    2. Hash check: rebuilds `ek = pk2 ‖ pk1[0..32]` and fails with `InvalidPublicKey` unless
       `H(ek) == pk1[32..64]` (`Fips203.Refinement.pk1HashValid`).
    3. Modulus check (FIPS 203 § 7.2): fails with `InvalidPublicKey` unless
       `ByteEncode₁₂(ByteDecode₁₂(pk2)) == pk2` (`Fips203.Refinement.pk2Valid`).

    The outer `Result` is always `ok` (the call never panics).

    **Modelling note**: steps 2 and 3 are modelled via the predicates
    `Fips203.Refinement.pk1HashValid` / `Fips203.Refinement.pk2Valid`; both always hold for keys
    produced by `from_seed` (`pk1HashValid_pk1Bytes`, `pk2Valid_pk2Bytes`). -/
@[rust_fun "libcrux_ml_kem::mlkem768::incremental::validate_pk_bytes"]
noncomputable def libcrux_ml_kem.mlkem768.incremental.validate_pk_bytes
  :
  Slice Std.U8 → Slice Std.U8 → Result (core.result.Result Unit
    libcrux_ml_kem.ind_cca.incremental.types.Error) :=
  fun pk1 pk2 =>
    if pk1.length ≠ 64 ∨ pk2.length ≠ 1152 then
      ok (.Err .InvalidInputLength)
    else if ¬ Fips203.Refinement.pk1HashValid pk1.val pk2.val then
      ok (.Err .InvalidPublicKey)
    else if ¬ Fips203.Refinement.pk2Valid pk2.val then
      ok (.Err .InvalidPublicKey)
    else
      ok (.Ok ())

/-- **Spec theorem for `libcrux_ml_kem::mlkem768::incremental::validate_pk_bytes`**:

- The call never panics (the outer `Result` is always `ok`).
- Returns `Err InvalidInputLength` if `pk1.len() ≠ 64` or `pk2.len() ≠ 1152`.
- Otherwise returns `Err InvalidPublicKey` if the header hash check
  `H(pk2 ‖ pk1[0..32]) = pk1[32..64]` (`Fips203.Refinement.pk1HashValid`) or the FIPS 203
  modulus check (`Fips203.Refinement.pk2Valid`) fails.
- Returns `Ok ()` iff the lengths are exact and both checks pass. -/
@[step]
theorem libcrux_ml_kem.mlkem768.incremental.validate_pk_bytes_spec
    (pk1 pk2 : Slice Std.U8) :
    libcrux_ml_kem.mlkem768.incremental.validate_pk_bytes pk1 pk2
      ⦃ (r : core.result.Result Unit libcrux_ml_kem.ind_cca.incremental.types.Error) =>
      (pk1.length ≠ 64 ∨ pk2.length ≠ 1152 → r = .Err .InvalidInputLength) ∧
      (pk1.length = 64 → pk2.length = 1152 →
        ¬ Fips203.Refinement.pk1HashValid pk1.val pk2.val → r = .Err .InvalidPublicKey) ∧
      (pk1.length = 64 → pk2.length = 1152 →
        ¬ Fips203.Refinement.pk2Valid pk2.val → r = .Err .InvalidPublicKey) ∧
      (r = .Ok () ↔ pk1.length = 64 ∧ pk2.length = 1152 ∧
        Fips203.Refinement.pk1HashValid pk1.val pk2.val ∧
        Fips203.Refinement.pk2Valid pk2.val) ⦄ := by
  unfold libcrux_ml_kem.mlkem768.incremental.validate_pk_bytes
  split
  · rename_i h
    simp only [WP.spec_ok]
    refine ⟨fun _ => trivial, fun h1 h2 _ => ?_, fun h1 h2 _ => ?_, ?_⟩
    · exact absurd h (by simp [h1, h2])
    · exact absurd h (by simp [h1, h2])
    · constructor
      · intro hc; cases hc
      · rintro ⟨h1, h2, -, -⟩; exact absurd h (by simp [h1, h2])
  · rename_i h
    rw [not_or, not_not, not_not] at h
    obtain ⟨h1, h2⟩ := h
    split <;> (try split) <;> simp_all [WP.spec_ok]

/-- [libcrux_ml_kem::mlkem768::incremental::encapsulate1]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/libcrux-ml-kem-0.0.7/src/mlkem.rs', lines 344:8-349:39
    Name pattern: [libcrux_ml_kem::mlkem768::incremental::encapsulate1] -/
@[rust_fun "libcrux_ml_kem::mlkem768::incremental::encapsulate1"]
noncomputable def libcrux_ml_kem.mlkem768.incremental.encapsulate1
  (pk1 : Slice Std.U8) (randomness : Array Std.U8 32#usize) (state : Slice Std.U8)
  (shared_secret : Slice Std.U8) :
  Result ((core.result.Result
    (libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1 960#usize)
    libcrux_ml_kem.ind_cca.incremental.types.Error) × (Slice Std.U8) × (Slice
    Std.U8)) :=
  -- Model: round 1 of FIPS 203 `ML-KEM.Encaps_internal` (`Fips203.mlkemEncapsPhase1`) on the
  -- header `pk1 = ρ ‖ H(ek)` and the message `randomness`, with libcrux's error behaviour:
  -- `InvalidInputLength` if `pk1.len() < 64` (`PublicKey1::try_from`), `InvalidOutputLength` if
  -- `shared_secret.len() < 32` or `state.len() < 2080` (`encapsulate1_serialized`,
  -- `EncapsState::to_bytes`).  On success `state[0:2080] := ŷ ‖ e₂ ‖ m`, `shared_secret[0:32]
  -- := K`, the remaining bytes are unchanged.  See `Spqr/Crypto/Fips203/Refinement/EncapsBytes.lean`.
  if h : 64 ≤ pk1.length then
    if h_ss : shared_secret.length < 32 then ok (.Err .InvalidOutputLength, state, shared_secret)
    else if h_st : state.length < Fips203.Refinement.encapsStateSize then
      ok (.Err .InvalidOutputLength, state, shared_secret)
    else
      let m := Fips203.Refinement.msgOfArray randomness
      ok (.Ok { value := Fips203.Refinement.ct1Array pk1.val h m },
        Slice.from (Fips203.Refinement.overwritePrefix state.val (Fips203.Refinement.stateOut pk1.val h m)) (by
          rw [Fips203.Refinement.overwritePrefix_length _ _ (Nat.not_lt.mp h_st)]
          exact state.length_ineq),
        Slice.from (Fips203.Refinement.overwritePrefix shared_secret.val (Fips203.Refinement.ssOut pk1.val h m)) (by
          rw [Fips203.Refinement.overwritePrefix_length _ _ (Nat.not_lt.mp h_ss)]
          exact shared_secret.length_ineq))
  else ok (.Err .InvalidInputLength, state, shared_secret)

/-- **Spec theorem for `libcrux_ml_kem::mlkem768::incremental::encapsulate1`**

- Never panics.
- Under the size preconditions `64 ≤ pk1.len()`, `32 ≤ shared_secret.len()`,
  `2080 ≤ state.len()` it returns `Ok(ct1)` where, writing `m = randomness` and
  `(K, c₁, (ŷ, e₂, m)) = mlkemEncapsPhase1 mlkem768 (ρ, h) m` for `pk1 = ρ ‖ h`
  (round 1 of FIPS 203 Algorithm 17):
  * `ct1.value = c₁` (`Fips203.Refinement.ct1List`), of length `960`;
  * the output `state` has the input's length, its first `2080` bytes are the serialised
    `ŷ ‖ e₂ ‖ m` (`Fips203.Refinement.stateOut`) and the rest is unchanged;
  * the output `shared_secret` has the input's length, its first `32` bytes are `K`
    (`Fips203.Refinement.ssOut`) and the rest is unchanged. -/
@[step]
theorem libcrux_ml_kem.mlkem768.incremental.encapsulate1_spec
    (pk1 : Slice Std.U8) (randomness : Array Std.U8 32#usize) (state : Slice Std.U8)
    (shared_secret : Slice Std.U8) (h_pk1 : 64 ≤ pk1.length)
    (h_ss : 32 ≤ shared_secret.length) (h_state : Fips203.Refinement.encapsStateSize ≤ state.length) :
    libcrux_ml_kem.mlkem768.incremental.encapsulate1 pk1 randomness state shared_secret
      ⦃ (r : (core.result.Result
          (libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1 960#usize)
          libcrux_ml_kem.ind_cca.incremental.types.Error) × (Slice Std.U8) × (Slice Std.U8)) =>
      r.1 = core.result.Result.Ok (libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1.mk
        (Fips203.Refinement.ct1Array pk1.val h_pk1 (Fips203.Refinement.msgOfArray randomness))) ∧
      r.2.1.val = Fips203.Refinement.overwritePrefix state.val
        (Fips203.Refinement.stateOut pk1.val h_pk1 (Fips203.Refinement.msgOfArray randomness)) ∧
      r.2.2.val = Fips203.Refinement.overwritePrefix shared_secret.val
        (Fips203.Refinement.ssOut pk1.val h_pk1 (Fips203.Refinement.msgOfArray randomness)) ∧
      r.2.1.length = state.length ∧
      r.2.2.length = shared_secret.length ⦄ := by
  simp only [Slice.from_val, Slice.length, libcrux_ml_kem.mlkem768.incremental.encapsulate1, dif_pos h_pk1,
    dif_neg (Nat.not_lt.mpr h_ss), dif_neg (Nat.not_lt.mpr h_state), WP.spec_ok]
  refine ⟨trivial, trivial, trivial, ?_, ?_⟩
  · exact Fips203.Refinement.overwritePrefix_length _ _ h_state
  · exact Fips203.Refinement.overwritePrefix_length _ _ h_ss

/-- [libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/libcrux-ml-kem-0.0.7/src/mlkem.rs', lines 439:8-443:30
    Name pattern: [libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key] -/
@[rust_fun "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key"]
noncomputable def libcrux_ml_kem.mlkem768.incremental.decapsulate_compressed_key
  (key_pair : Array Std.U8 2400#usize)
  (ciphertext1 : libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1 960#usize)
  (ciphertext2 : libcrux_ml_kem.ind_cca.incremental.types.Ciphertext2 128#usize) :
  Result (Array Std.U8 32#usize) :=
  -- Model: FIPS 203 `ML-KEM.Decaps_internal` (`Fips203.mlkemDecaps`, Algorithm 18) on the
  -- decapsulation key read from the 2400-byte compressed key-pair buffer and the reassembled
  -- ciphertext `c = c₁ ‖ c₂`.  All inputs are fixed-size arrays, so there are no error cases
  -- and the function never fails.  Note that this is `Decaps_internal`, not `ML-KEM.Decaps`
  -- (Algorithm 21): the FIPS 203 § 7.3 hash check `H(dk[1152:2336]) = dk[2336:2368]` is
  -- not performed by libcrux's `decapsulate_compressed_key`, so the model admits any
  -- 2400-byte `key_pair`.  See `Spqr/Crypto/Fips203/Refinement/DecapsBytes.lean`.
  ok (Fips203.Refinement.ssArray key_pair ciphertext1.value ciphertext2.value)

/-- **Spec theorem for `libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key`**

- Never panics (all inputs are fixed-size arrays, so there are no length checks).
- Returns the 32-byte shared secret of FIPS 203 Algorithm 18 (`Fips203.mlkemDecaps`) on the
  decapsulation key stored in `key_pair` and the ciphertext `c₁ ‖ c₂`
  (`Fips203.Refinement.ssList`). -/
@[step]
theorem libcrux_ml_kem.mlkem768.incremental.decapsulate_compressed_key_spec
    (key_pair : Array Std.U8 2400#usize)
    (ciphertext1 : libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1 960#usize)
    (ciphertext2 : libcrux_ml_kem.ind_cca.incremental.types.Ciphertext2 128#usize) :
    libcrux_ml_kem.mlkem768.incremental.decapsulate_compressed_key key_pair ciphertext1
      ciphertext2
      ⦃ (ss : Array Std.U8 32#usize) =>
      ss.length = 32 ∧
      ss.val = Fips203.Refinement.ssList key_pair ciphertext1.value ciphertext2.value ⦄ := by
  simp only [libcrux_ml_kem.mlkem768.incremental.decapsulate_compressed_key, WP.spec_ok]
  exact ⟨Array.length_eq _, rfl⟩

/-- [sorted_vec::{core::clone::Clone for sorted_vec::SortedSet<T>}::clone]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/sorted-vec-0.8.6/src/lib.rs', lines 38:9-38:14
    Name pattern: [sorted_vec::{core::clone::Clone<sorted_vec::SortedSet<@T>>}::clone] -/
@[rust_fun
  "sorted_vec::{core::clone::Clone<sorted_vec::SortedSet<@T>>}::clone"]
noncomputable opaque sorted_vec.SortedSet.Insts.CoreCloneClone.clone
  {T : Type} (corecloneCloneInst : core.clone.Clone T) (corecmpOrdInst :
  core.cmp.Ord T) :
  sorted_vec.SortedSet T → Result (sorted_vec.SortedSet T)

/-- [sorted_vec::{core::ops::deref::Deref<alloc::vec::Vec<T>> for sorted_vec::SortedVec<T>}::deref]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/sorted-vec-0.8.6/src/lib.rs', lines 309:2-309:30
    Name pattern: [sorted_vec::{core::ops::deref::Deref<sorted_vec::SortedVec<@T>, alloc::vec::Vec<@T>>}::deref]

    Concrete model of Rust's `<SortedVec<T> as Deref>::deref`: returns the
    inner `Vec<T>`.  Since `SortedVec T` is definitionally equal to
    `alloc.vec.Vec T` in the Lean model, `deref` is simply the identity
    function. The outer `Result` is always `ok` (the call never panics). -/
@[rust_fun
  "sorted_vec::{core::ops::deref::Deref<sorted_vec::SortedVec<@T>, alloc::vec::Vec<@T>>}::deref"]
def sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref
  {T : Type} (_corecmpOrdInst : core.cmp.Ord T) :
  sorted_vec.SortedVec T → Result (alloc.vec.Vec T) :=
  fun sv => ok sv

/-- **Spec theorem for `<SortedVec<T> as Deref>::deref`**: since `SortedVec T`
    is modelled as `alloc.vec.Vec T`, `deref` is the identity. -/
@[simp, step_simps, step]
theorem sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref_spec
    {T : Type} (corecmpOrdInst : core.cmp.Ord T)
    (s : sorted_vec.SortedVec T) :
    sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref corecmpOrdInst s
      ⦃ (v : alloc.vec.Vec T) => v = s ⦄ := by
  unfold sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref
  exact (WP.spec_ok _).mpr rfl


/-- [sorted_vec::{sorted_vec::SortedSet<T>}::new]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/sorted-vec-0.8.6/src/lib.rs', lines 347:2-347:22
    Name pattern: [sorted_vec::{sorted_vec::SortedSet<@T>}::new]

    Concrete model of Rust's `SortedSet::new()`: returns an empty `SortedSet`.
    Since `SortedSet T = SortedVec T = alloc.vec.Vec T`, this is just the
    empty vector wrapped in `ok`. -/
@[rust_fun "sorted_vec::{sorted_vec::SortedSet<@T>}::new"]
def sorted_vec.SortedSet.new
  {T : Type} (_corecmpOrdInst : core.cmp.Ord T) :
  Result (sorted_vec.SortedSet T) :=
  ok (alloc.vec.Vec.new T)

/-- **Spec theorem for `sorted_vec.SortedSet.new`**:
    the call always succeeds and returns the empty set (empty `Vec`). -/
@[simp, step_simps]
theorem sorted_vec.SortedSet.new_spec
    {T : Type} (corecmpOrdInst : core.cmp.Ord T) :
    sorted_vec.SortedSet.new corecmpOrdInst ⦃ (s : sorted_vec.SortedSet T) =>
      s = alloc.vec.Vec.new T ⦄ := by
  unfold sorted_vec.SortedSet.new
  exact (WP.spec_ok _).mpr rfl

/-- [sorted_vec::{sorted_vec::SortedSet<T>}::with_capacity]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/sorted-vec-0.8.6/src/lib.rs', lines 351:2-351:49
    Name pattern: [sorted_vec::{sorted_vec::SortedSet<@T>}::with_capacity]

    Concrete model of Rust's `SortedSet::with_capacity(capacity)`: returns an
    empty `SortedSet` with pre-allocated space for `capacity` elements.
    Since `SortedSet T = SortedVec T = alloc.vec.Vec T` and we do not track
    capacity in the Lean model, this is identical to `SortedSet::new()`.
    The outer `Result` is always `ok` (the call never panics: its only failure
    mode is allocation failure, which aborts rather than returning). -/
@[rust_fun "sorted_vec::{sorted_vec::SortedSet<@T>}::with_capacity"]
def sorted_vec.SortedSet.with_capacity
  {T : Type} (_corecmpOrdInst : core.cmp.Ord T) :
  Std.Usize → Result (sorted_vec.SortedSet T) :=
  fun _ => ok (alloc.vec.Vec.new T)


/-- **Spec theorem for `SortedSet::with_capacity`**: the call always succeeds
    and returns the empty set (empty `Vec`), ignoring the capacity hint. -/
@[simp, step_simps, step]
theorem sorted_vec.SortedSet.with_capacity_spec
    {T : Type} (corecmpOrdInst : core.cmp.Ord T) (n : Std.Usize) :
    sorted_vec.SortedSet.with_capacity corecmpOrdInst n
      ⦃ (s : sorted_vec.SortedSet T) => s = alloc.vec.Vec.new T ⦄ := by
  unfold sorted_vec.SortedSet.with_capacity
  exact (WP.spec_ok _).mpr rfl

/-- Helper: sorted insertion into a sorted list, modelling `SortedVec::replace`
    (sorted-vec 0.8.6, `src/lib.rs`, lines 362-376).

    Scans the list left-to-right (modelling binary search on sorted data) using
    the `Ord` instance's `cmp` method to find the correct position for `x`.
    Returns `(index, displaced_option, updated_list)`:
    - If an equal element exists at position `i`, it is replaced:
      result is `(i, some old_element, list_with_replacement)`.
    - Otherwise the element is inserted at its sorted position `i`:
      result is `(i, none, list_with_insertion)`. -/
def sorted_vec.SortedSet.sortedInsert {T : Type}
    (cmpOrdInst : core.cmp.Ord T) :
    List T → T → Nat → Result (Nat × Option T × List T)
  | [], x, i => ok (i, none, [x])
  | a :: rest, x, i => do
    let ord ← cmpOrdInst.cmp a x
    match ord with
    | .gt => ok (i, none, x :: a :: rest)
    | .eq => ok (i, some a, x :: rest)
    | .lt => do
      let (idx, opt, rest') ←
        sorted_vec.SortedSet.sortedInsert cmpOrdInst rest x (i + 1)
      ok (idx, opt, a :: rest')

/-- Spec lemma for `sortedInsert`: if `sortedInsert cmpOrdInst list x i` succeeds
    with result `(idx, opt, newList)`, then there exists `k` such that `idx = i + k`,
    `k ≤ list.length`, and `newList` is `list` with `x` either inserted at position `k`
    (when `opt = none`) or replacing the element at position `k` (when `opt = some _`). -/
theorem sorted_vec.SortedSet.sortedInsert_spec {T : Type}
    (cmpOrdInst : core.cmp.Ord T)
    (list : List T) (x : T) (i : Nat)
    {idx : Nat} {opt : Option T} {newList : List T}
    (h : sorted_vec.SortedSet.sortedInsert cmpOrdInst list x i =
         ok (idx, opt, newList)) :
    ∃ k, idx = i + k ∧ k ≤ list.length ∧
      (newList = list.take k ++ [x] ++ list.drop k ∨
       (k < list.length ∧
        newList = list.take k ++ [x] ++ list.drop (k + 1))) := by
  induction list generalizing i idx opt newList with
  | nil =>
    simp only [sortedInsert, Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨0, by omega, by omega, Or.inl (by simp)⟩
  | cons a rest ih =>
    simp only [sortedInsert] at h
    cases h_cmp : cmpOrdInst.cmp a x with
    | ret ord =>
      simp only [h_cmp, bind_ok] at h
      rcases ord with _ | _ | _
      · -- Ordering.lt: recursive case. Case on `Result.match` of the recursive call (an
        -- inductive view) rather than on the coinductive `Result` itself.
        cases hr : (sorted_vec.SortedSet.sortedInsert cmpOrdInst rest x (i + 1)).match with
        | ok r =>
          obtain ⟨idx', opt', rest'⟩ := r
          rw [Result.match.isOk] at hr
          simp only [hr, bind_ok, uncurry_apply_pair, ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨k, hk_idx, hk_le, hk_prop⟩ := ih (i + 1) hr
          refine ⟨k + 1, by omega, by grind, ?_⟩
          rcases hk_prop with h_ins | ⟨h_lt, h_rep⟩
          · exact Or.inl (by simp [h_ins])
          · exact Or.inr ⟨by grind, by simp [h_rep]⟩
        | div => rw [Result.match.isDiv] at hr; simp [hr] at h
        | vis e kk => rw [Result.match.isVis] at hr; simp [hr] at h
      · -- Ordering.eq: replace in place
        simp only [Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨0, by omega, by omega, Or.inr ⟨by simp, by simp⟩⟩
      · -- Ordering.gt: insert before
        simp only [Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨0, by omega, by omega, Or.inl (by simp)⟩
    | vis e k => simp [h_cmp] at h
    | div => simp [h_cmp] at h

/-- [sorted_vec::{sorted_vec::SortedSet<T>}::push]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/sorted-vec-0.8.6/src/lib.rs', lines 392:2-392:58
    Name pattern: [sorted_vec::{sorted_vec::SortedSet<@T>}::push]

    Concrete model of Rust's `SortedSet::push`: inserts an element into the
    sorted set.  The method first compares the element with the last element
    of the underlying vector to determine the appropriate action:

    Rust source (sorted-vec 0.8.6, `src/lib.rs`, lines 388-417):
    ```rust
    pub fn push(&mut self, element: T) -> (usize, Option<T>) {
      if let Some(last) = self.vec.last() {
        let cmp = element.cmp(last);
        if cmp == std::cmp::Ordering::Greater {
          self.set.vec.push(element);
          return (self.vec.len() - 1, None);
        } else if cmp == std::cmp::Ordering::Equal {
          let original = self.set.vec.pop();
          self.set.vec.push(element);
          return (self.vec.len() - 1, original);
        } else {
          return self.replace(element);
        }
      } else {
        self.set.vec.push(element);
        return (0, None);
      }
    }
    ```

    The model covers all four branches:

    - **Empty** (`vec.last() = None`): pushes the element and returns `(0, None)`.
    - **Greater** (`element > last`): appends to the back (O(1) fast path) and
      returns `(old_length, None)`.
    - **Equal** (`element == last`): replaces the last element (pop + push) and
      returns `(old_length - 1, Some(last))`.
    - **Less** (`element < last`): falls back to `replace` (modelled by
      `sortedInsert`, a linear scan matching binary search on sorted data)
      which either inserts at the sorted position or replaces an equal element.

    Fails if the vector would overflow `Usize.max`. -/
@[rust_fun "sorted_vec::{sorted_vec::SortedSet<@T>}::push"]
def sorted_vec.SortedSet.push
  {T : Type} (corecmpOrdInst : core.cmp.Ord T) :
  sorted_vec.SortedSet T → T → Result ((Std.Usize × (Option T)) ×
    (sorted_vec.SortedSet T)) :=
  fun s x =>
    if hroom : s.val.length + 1 ≤ Usize.max then
      match hm : s.val.getLast? with
      | none =>
        -- Container is empty: push the element and return (0, None)
        ok ((0#usize, none),
            alloc.vec.Vec.from (s.val ++ [x]) (by
              simp only [List.length_append, List.length_cons, List.length_nil, zero_add]
              scalar_tac))
      | some last => do
        -- Non-empty: compare element with last
        let ord ← corecmpOrdInst.cmp x last
        match ord with
        | .gt =>
          -- element > last: push to back, O(1) fast path
          ok ((⟨s.val.length, by scalar_tac⟩, none),
              alloc.vec.Vec.from (s.val ++ [x]) (by
                simp only [List.length_append, List.length_cons, List.length_nil, zero_add]
                scalar_tac))
        | .eq =>
          -- element == last: pop last, push element (replace last with element)
          ok ((⟨s.val.length - 1, by
                have := s.property
                have : s.val ≠ [] := by intro h; simp [h] at hm
                scalar_tac⟩, some last),
              alloc.vec.Vec.from (s.val.dropLast ++ [x]) (by
                have := s.property
                simp only [List.length_append, List.length_cons, List.length_nil,
                  List.length_dropLast, zero_add]; omega))
        | .lt => do
          -- element < last: fall back to replace (sorted insert via binary search)
          let (idx, opt, newList) ← sorted_vec.SortedSet.sortedInsert corecmpOrdInst s.val x 0
          dite (newList.length ≤ Usize.max ∧ idx ≤ Usize.max)
            (fun hbnd => ok ((⟨idx, by have := hbnd.2; grind⟩, opt),
              alloc.vec.Vec.from newList hbnd.1))
            (fun _ => fail .panic)
    else
      fail .panic

/-- **Spec theorem for `SortedSet::push` (empty case)**:
    when the set is empty (`getLast? = none`), the call pushes the element
    and returns `(0, none)` together with the set `s ++ [x]` (which equals
    `[x]` since `s` is empty). -/
@[step]
theorem sorted_vec.SortedSet.push_spec_empty
    {T : Type} (corecmpOrdInst : core.cmp.Ord T)
    (s : sorted_vec.SortedSet T) (x : T)
    (h : s.val.length + 1 ≤ Usize.max)
    (hempty : s.val.getLast? = none) :
    sorted_vec.SortedSet.push corecmpOrdInst s x ⦃ ((n, o), s') =>
      n.val = 0 ∧
      o = none ∧
      s'.val = s.val ++ [x] ⦄ := by
  unfold sorted_vec.SortedSet.push
  simp only [dite_eq_left h]
  split
  · next h_none =>
    have he : s.val = [] := by
      cases hs : s.val with
      | nil => rfl
      | cons _ _ => simp [hs, List.getLast?] at h_none
    simp only [he, List.nil_append, WP.spec_ok]
    exact ⟨rfl, rfl, rfl⟩
  · next last h_some => simp [h_some] at hempty

/-- **Spec theorem for `SortedSet::push` (greater case)**:
    when the set is non-empty and the new element compares as `Greater`
    than the last element (`cmp x last = ok .gt`), the call appends `x`
    to the back (O(1) fast path) and returns `(old_length, none)` together
    with the set extended by `x`.  The `none` indicates no duplicate was
    displaced. -/
@[step]
theorem sorted_vec.SortedSet.push_spec_gt
    {T : Type} (corecmpOrdInst : core.cmp.Ord T)
    (s : sorted_vec.SortedSet T) (x : T)
    (h : s.val.length + 1 ≤ Usize.max)
    (last : T) (hlast : s.val.getLast? = some last)
    (hcmp : corecmpOrdInst.cmp x last = ok .gt) :
    sorted_vec.SortedSet.push corecmpOrdInst s x ⦃ ((n, o), s') =>
      n.val = s.val.length ∧
      o = none ∧
      s'.val = s.val ++ [x] ⦄ := by
  unfold sorted_vec.SortedSet.push
  simp only [dite_eq_left h]
  split
  · next h_none => simp [h_none] at hlast
  · next last' h_some =>
    have : last' = last := by
      have := h_some.symm.trans hlast; simp only [Option.some.injEq] at this; exact this
    subst this
    simp only [hcmp, bind_ok, WP.spec_ok]
    refine ⟨rfl, rfl, ?_⟩
    simp

/-- **Spec theorem for `SortedSet::push` (equal case)**:
    when the set is non-empty and the new element compares as `Equal`
    to the last element (`cmp x last = ok .eq`), the call replaces the
    last element with `x` (pop + push) and returns
    `(old_length - 1, some last)` together with the set where the last
    element has been replaced.  The `some last` carries the displaced
    duplicate. -/
@[step]
theorem sorted_vec.SortedSet.push_spec_eq
    {T : Type} (corecmpOrdInst : core.cmp.Ord T)
    (s : sorted_vec.SortedSet T) (x : T)
    (h : s.val.length + 1 ≤ Usize.max)
    (last : T) (hlast : s.val.getLast? = some last)
    (hcmp : corecmpOrdInst.cmp x last = ok .eq) :
    sorted_vec.SortedSet.push corecmpOrdInst s x ⦃ ((n, o), s') =>
      n.val = s.val.length - 1 ∧
      o = some last ∧
      s'.val = s.val.dropLast ++ [x] ⦄ := by
  unfold sorted_vec.SortedSet.push
  simp only [dite_eq_left h]
  split
  · next h_none => simp [h_none] at hlast
  · next last' h_some =>
    have : last' = last := by
      have := h_some.symm.trans hlast; simp only [Option.some.injEq] at this; exact this
    subst this
    simp only [hcmp, bind_ok, WP.spec_ok]
    refine ⟨rfl, rfl, ?_⟩
    simp

/-- **Spec theorem for `SortedSet::push` (less case)**:
    when the set is non-empty and the new element compares as `Less`
    than the last element (`cmp x last = ok .lt`), the call falls back
    to `sortedInsert` (modelling binary search on sorted data).  The
    result is `(idx, opt)` together with the updated list `newList`,
    where `idx` is the insertion/replacement position, `opt` is `none`
    for a fresh insertion or `some old_elem` for a replacement, and
    `newList` is the updated element list. -/
@[step]
theorem sorted_vec.SortedSet.push_spec_lt
    {T : Type} (corecmpOrdInst : core.cmp.Ord T)
    (s : sorted_vec.SortedSet T) (x : T)
    (h : s.val.length + 1 ≤ Usize.max)
    (last : T) (hlast : s.val.getLast? = some last)
    (hcmp : corecmpOrdInst.cmp x last = ok .lt)
    (idx : Nat) (opt : Option T) (newList : List T)
    (hsorted : sorted_vec.SortedSet.sortedInsert corecmpOrdInst s.val x 0 =
      ok (idx, opt, newList))
    (hbnd : newList.length ≤ Usize.max ∧ idx ≤ Usize.max) :
    sorted_vec.SortedSet.push corecmpOrdInst s x ⦃ ((n, o), s') =>
      n.val = idx ∧
      o = opt ∧
      s'.val = newList ⦄ := by
  unfold sorted_vec.SortedSet.push
  simp only [dite_eq_left h]
  split
  · next h_none => simp [h_none] at hlast
  · next last' h_some =>
    have : last' = last := by
      have := h_some.symm.trans hlast; simp only [Option.some.injEq] at this; exact this
    subst this
    simp only [hcmp, bind_ok, hsorted]
    simp only [UScalarTy.Usize_numBits_eq, uncurry_apply_pair, hbnd, and_true, ↓reduceDIte,
      WP.spec_ok]
    exact ⟨rfl, rfl, by simp⟩

/-- **Spec theorem for `SortedSet::push` (Greater / empty combined)**:
    when the set is either empty or the new element compares as `Greater`
    than the last element (the O(1) fast path), the call succeeds and
    returns `(old_length, none)` together with the set extended by `x`.
    The `none` indicates no duplicate was displaced.

    The hypothesis `hcmp` asserts that every `last` returned by `getLast?`
    compares as less than `x` (i.e., `cmp x last = ok .gt`). This is
    trivially satisfied when the set is empty (vacuous) and must be
    established by the caller when the set is non-empty.

    See also `push_spec_empty`, `push_spec_gt`, `push_spec_eq`, and
    `push_spec_lt` for per-branch spec theorems that match every case
    of the definition. -/
@[step]
theorem sorted_vec.SortedSet.push_spec
    {T : Type} (corecmpOrdInst : core.cmp.Ord T)
    (s : sorted_vec.SortedSet T) (x : T)
    (h : s.val.length + 1 ≤ Usize.max)
    (hcmp : ∀ last, s.val.getLast? = some last →
      corecmpOrdInst.cmp x last = ok .gt) :
    sorted_vec.SortedSet.push corecmpOrdInst s x ⦃ ((n, o), s') =>
      n.val = s.val.length ∧
      o = none ∧
      s'.val = s.val ++ [x] ⦄ := by
  unfold sorted_vec.SortedSet.push
  simp only [dite_eq_left h]
  split
  · next hlast =>
    have he : s.val = [] := by
      cases hs : s.val with
      | nil => rfl
      | cons _ _ => simp [hs, List.getLast?] at hlast
    simp only [he, List.nil_append, List.length_nil, WP.spec_ok]
    exact ⟨rfl, rfl, rfl⟩
  · next last hlast =>
    simp only [hcmp last hlast, bind_ok, WP.spec_ok]
    refine ⟨rfl, rfl, ?_⟩
    simp

/-- [sorted_vec::{core::ops::deref::Deref<sorted_vec::SortedVec<T>> for sorted_vec::SortedSet<T>}::deref]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/sorted-vec-0.8.6/src/lib.rs', lines 543:2-543:36
    Name pattern: [sorted_vec::{core::ops::deref::Deref<sorted_vec::SortedSet<@T>, sorted_vec::SortedVec<@T>>}::deref]

    Concrete model of Rust's `<SortedSet<T> as Deref<Target = SortedVec<T>>>::deref`:
    returns the inner `SortedVec<T>`.  Since `SortedSet T` is definitionally
    equal to `SortedVec T` in the Lean model, this is the identity function.
    The outer `Result` is always `ok` (the call never panics). -/
@[rust_fun
  "sorted_vec::{core::ops::deref::Deref<sorted_vec::SortedSet<@T>, sorted_vec::SortedVec<@T>>}::deref"]
def sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref
  {T : Type} (_corecmpOrdInst : core.cmp.Ord T) :
  sorted_vec.SortedSet T → Result (sorted_vec.SortedVec T) :=
  fun s => ok s

/-- **Spec theorem for `<SortedSet<T> as Deref>::deref`**: the call always
    succeeds and returns the set itself (since `SortedSet T` and `SortedVec T`
    are definitionally equal in the Lean model). -/
@[simp, step_simps, step]
theorem sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref_spec
    {T : Type} (corecmpOrdInst : core.cmp.Ord T)
    (s : sorted_vec.SortedSet T) :
    sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref corecmpOrdInst s
      ⦃ (v : sorted_vec.SortedVec T) => v = s ⦄ := by
  unfold sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref
  exact (WP.spec_ok _).mpr rfl

/-- [thiserror::display::{thiserror::display::AsDisplay<'a, &'a (T)> for &1 (T)}::as_display]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/thiserror-2.0.12/src/display.rs', lines 20:4-20:43
    Name pattern: [thiserror::display::{thiserror::display::AsDisplay<'a, &'0 @T, &'a @T>}::as_display] -/
@[rust_fun
  "thiserror::display::{thiserror::display::AsDisplay<'a, &'0 @T, &'a @T>}::as_display"]
noncomputable opaque Shared0T.Insts.ThiserrorDisplayAsDisplayASharedAT.as_display
  {T : Type} (corefmtDisplayInst : core.fmt.Display T) : T → Result T

namespace spqr.kdf

/- See `hkdf_to_slice_spec` in `Spqr/Specs/Kdf/HkdfToSlice.lean`: this function implements
RFC 5869. -/

/-- [spqr::kdf::hkdf_to_slice]:
    Source: 'src/kdf.rs', lines 14:0-18:1
    Visibility: public -/
noncomputable opaque hkdf_to_slice : Slice Std.U8 → Slice Std.U8 → Slice Std.U8 → Slice Std.U8 →
    Result (Slice Std.U8)

end spqr.kdf

/-- [spqr::incremental_mlkem768::potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275]:
    Source: 'src/incremental_mlkem768.rs', lines 92:0-138:1

    SPQR's own (not libcrux's) endianness workaround for libcrux issue #1275, marked
    `#[hax_lib::opaque]` in the Rust source.  It scans the `error₂` region
    `es[1536 .. 2048]` in 2-byte little-endian words:
    * `0x0000` / `0xFFFF` are skipped (identical in both endiannesses);
    * `0x0001` / `0x0002` / `0xFFFE` ⇒ the state is correctly encoded, return `None`;
    * `0x0100` / `0x0200` / `0xFEFF` ⇒ the state is byte-swapped, return
      `Some (flip_endianness_of_encapsulation_state es)`;
    * any other word ⇒ "weird state", return `None`.

    The function is kept **uninterpreted** here: on byte-swapped states it genuinely returns
    `Some`, so any concrete stub (e.g. `fun _ => ok none`) would be an unsound model and would
    let downstream specs claim `encaps2` consumes `es` itself on states the Rust repairs.  The
    only property assumed is the hax contract (`potentially_fix_state_…_spec` below). -/
@[rust_fun "spqr::incremental_mlkem768::potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275"]
noncomputable opaque
  incremental_mlkem768.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275
  : alloc.vec.Vec Std.U8 → Result (Option (alloc.vec.Vec Std.U8))

/-- **Trusted spec axiom for `potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`**:

Exactly the hax contract from `src/incremental_mlkem768.rs`, lines 85-90:
- **requires**: `es.len() == 2080`
- **ensures**: `|result| if let Some(es) = result { es.len() == 2080 } else { true }`

Under the length precondition the call succeeds (the only panic site is
`assert_eq!(es.len(), 2080)`, discharged by `h_es`; `chunks(2)` on the 512-byte region and
`try_into` on each 2-byte chunk cannot fail) and returns `mf : Option (Vec U8)` such that any
`Some v` has `v.length = 2080` (`flip_endianness_of_encapsulation_state` preserves length, see
`flip_endianness_of_encapsulation_state_spec`).  Nothing is assumed about *which* of
`None` / `Some (flipped es)` is returned. -/
@[step]
axiom incremental_mlkem768.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_spec
    (es : alloc.vec.Vec Std.U8) (h_es : es.length = 2080) :
    incremental_mlkem768.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 es
      ⦃ (mf : Option (alloc.vec.Vec Std.U8)) => ∀ v ∈ mf, v.length = 2080 ⦄

/- See `Spqr/Specs/Lib/StatePb.lean`: these wrap prost's `encode_to_vec`/`decode` for the ratchet
state (translation patch `lib-state_pb.patch`). -/

/-- [spqr::encode_state_pb]:
    Source: 'src/lib.rs', lines 50:0-52:1 -/
noncomputable opaque encode_state_pb
  : proto.pq_ratchet.PqRatchetState → Result (alloc.vec.Vec Std.U8)

/-- [spqr::decode_state_pb]:
    Source: 'src/lib.rs', lines 54:0-56:1 -/
noncomputable opaque decode_state_pb
  :
  Slice Std.U8 → Result (core.result.Result proto.pq_ratchet.PqRatchetState
    prost.error.DecodeError)

-- Models for `VecDeque` iteration
/-- [alloc::collections::vec_deque::into_iter::{core::iter::traits::iterator::Iterator<T> for alloc::collections::vec_deque::into_iter::IntoIter<T, A>}::next]:
    Source: '/rustc/library/alloc/src/collections/vec_deque/into_iter.rs', lines 47:4-47:35
    Name pattern: [alloc::collections::vec_deque::into_iter::{core::iter::traits::iterator::Iterator<alloc::collections::vec_deque::into_iter::IntoIter<@T, @A>, @T>}::next] -/
@[rust_fun
  "alloc::collections::vec_deque::into_iter::{core::iter::traits::iterator::Iterator<alloc::collections::vec_deque::into_iter::IntoIter<@T, @A>, @T>}::next"]
def
  alloc.collections.vec_deque.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
  {T : Type} {A : Type}
  (intoIter: alloc.collections.vec_deque.into_iter.IntoIter T A):
    Result ((Option T) × (alloc.collections.vec_deque.into_iter.IntoIter T A)) :=
        let deq: alloc.collections.vec_deque.VecDeque T A := intoIter.inner
        -- Growing-list model (consistent with pop_front / push_back):
        -- `head` advances linearly, `length` decrements, no wrap-around.
        if (deq.length == 0#usize) then ok (none, intoIter)
        else
          if hidx : deq.head < deq.buf.length then
            do
              let elem := deq.buf.val[deq.head.val]'hidx
              let head' ← deq.head + 1#usize
              let len'  ← deq.length - 1#usize
              let newInner: alloc.collections.vec_deque.VecDeque T A := {
                buf := deq.buf,
                head := head',
                length := len'
              }
              ok (some elem, {inner := newInner})
          else
            fail .panic

/-- [alloc::collections::vec_deque::into_iter::{core::iter::traits::iterator::Iterator<T> for alloc::collections::vec_deque::into_iter::IntoIter<T, A>}::map]:
    Source: '/rustc/library/alloc/src/collections/vec_deque/into_iter.rs', lines 43:0-43:49
    Name pattern: [alloc::collections::vec_deque::into_iter::{core::iter::traits::iterator::Iterator<alloc::collections::vec_deque::into_iter::IntoIter<@T, @A>, @T>}::map] -/
@[rust_fun
  "alloc::collections::vec_deque::into_iter::{core::iter::traits::iterator::Iterator<alloc::collections::vec_deque::into_iter::IntoIter<@T, @A>, @T>}::map"]
def
  alloc.collections.vec_deque.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.map
  {T : Type} {A : Type} {B : Type} {F : Type}
  (coreopsfunctionFnMutFTupleTBInst: core.ops.function.FnMut F T B)
  (intoIter: alloc.collections.vec_deque.into_iter.IntoIter T A)
  (fn: F): Result (core.iter.adapters.map.Map (alloc.collections.vec_deque.into_iter.IntoIter T A) F) :=
    ok {iter:= intoIter, f:= fn}

/-- [alloc::collections::vec_deque::{core::iter::traits::collect::FromIterator<T> for alloc::collections::vec_deque::VecDeque<T, alloc::alloc::Global>}::from_iter]:
    Source: '/rustc/library/alloc/src/collections/vec_deque/mod.rs', lines 3641:4-3641:67
    Name pattern: [alloc::collections::vec_deque::{core::iter::traits::collect::FromIterator<alloc::collections::vec_deque::VecDeque<@T, alloc::alloc::Global>, @T>}::from_iter] -/
@[rust_fun
  "alloc::collections::vec_deque::{core::iter::traits::collect::FromIterator<alloc::collections::vec_deque::VecDeque<@T, alloc::alloc::Global>, @T>}::from_iter"]
def
  alloc.collections.vec_deque.VecDequeTGlobal.Insts.CoreIterTraitsCollectFromIterator.from_iter
  {T : Type} {I : Type} {Clause0_IntoIter : Type}
  (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I T Clause0_IntoIter) :
  I → Result (alloc.collections.vec_deque.VecDeque T Global) :=
  fun input => do
    let v ← alloc.vec.FromIteratorVec.from_iter
              coreitertraitscollectIntoIteratorInst input
    ok ({ buf := v,
          head := 0#usize,
          length := Std.Usize.ofNatCore v.length
            (by have := v.property; scalar_tac) }
        : alloc.collections.vec_deque.VecDeque T Global)

/-- Spec for `VecDeque::from_iter`: if the underlying `Vec` collection
    yields `v`, the returned deque has `buf = v`, `head = 0`, and
    `length = v.length`. -/
@[step]
theorem alloc.collections.vec_deque.VecDequeTGlobal.Insts.CoreIterTraitsCollectFromIterator.from_iter_spec
    {T I Clause0_IntoIter : Type}
    (inst : core.iter.traits.collect.IntoIterator I T Clause0_IntoIter)
    (input : I) (v : alloc.vec.Vec T)
    (hv : alloc.vec.FromIteratorVec.from_iter inst input = ok v) :
    alloc.collections.vec_deque.VecDequeTGlobal.Insts.CoreIterTraitsCollectFromIterator.from_iter
      inst input ⦃ (vd : alloc.collections.vec_deque.VecDeque T Global) =>
      vd.buf = v ∧
      vd.head = 0#usize ∧
      vd.length.val = v.val.length ⦄ := by
  unfold alloc.collections.vec_deque.VecDequeTGlobal.Insts.CoreIterTraitsCollectFromIterator.from_iter
  rw [hv]
  simp


/-- `IntoIter::new`: wraps a `VecDeque T A` into the opaque `IntoIter T A`. -/
def alloc.collections.vec_deque.into_iter.IntoIter.new
  {T A : Type} :
  alloc.collections.vec_deque.VecDeque T A →
    alloc.collections.vec_deque.into_iter.IntoIter T A :=
  fun vd => ⟨vd⟩

/-- Spec for `IntoIter::new`: returns the structure `⟨vd⟩`. -/
@[simp, step_simps]
theorem alloc.collections.vec_deque.into_iter.IntoIter.new_spec
    {T A : Type} (vd : alloc.collections.vec_deque.VecDeque T A) :
    alloc.collections.vec_deque.into_iter.IntoIter.new vd = ⟨vd⟩ := rfl

/-- [alloc::collections::vec_deque::{core::iter::traits::collect::IntoIterator<T, alloc::collections::vec_deque::into_iter::IntoIter<T, A>> for alloc::collections::vec_deque::VecDeque<T, A>}::into_iter]:
    Source: '/rustc/library/alloc/src/collections/vec_deque/mod.rs', lines 3653:4-3653:40
    Name pattern: [alloc::collections::vec_deque::{core::iter::traits::collect::IntoIterator<alloc::collections::vec_deque::VecDeque<@T, @A>, @T, alloc::collections::vec_deque::into_iter::IntoIter<@T, @A>>}::into_iter] -/
@[rust_fun
  "alloc::collections::vec_deque::{core::iter::traits::collect::IntoIterator<alloc::collections::vec_deque::VecDeque<@T, @A>, @T, alloc::collections::vec_deque::into_iter::IntoIter<@T, @A>>}::into_iter"]
def alloc.collections.vec_deque.VecDeque.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
  {T : Type} {A : Type} :
  alloc.collections.vec_deque.VecDeque T A → Result
    (alloc.collections.vec_deque.into_iter.IntoIter T A) :=
  fun self => ok (alloc.collections.vec_deque.into_iter.IntoIter.new self)

/-- Spec for `VecDeque::into_iter`: always returns `IntoIter.new vd`. -/
@[simp, step_simps]
theorem
  alloc.collections.vec_deque.VecDeque.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter_spec
    {T A : Type} (vd : alloc.collections.vec_deque.VecDeque T A) :
    alloc.collections.vec_deque.VecDeque.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
        vd
      ⦃ (iter : alloc.collections.vec_deque.into_iter.IntoIter T A) =>
        iter = alloc.collections.vec_deque.into_iter.IntoIter.new vd ⦄ := by
  simp [alloc.collections.vec_deque.VecDeque.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter]
