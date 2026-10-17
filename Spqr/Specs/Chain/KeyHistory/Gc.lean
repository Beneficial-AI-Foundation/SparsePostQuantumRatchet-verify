/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
import Spqr.Specs.Chain.KeyHistory.KEY_SIZE
import Spqr.Specs.Chain.ChainParams.TrimSize
import Spqr.Specs.Chain.ChainParams.MaxOooKeysOrDefault
import Spqr.Specs.Aeneas.IndexRangeFull
import Spqr.Specs.Chain.KeyHistory.Remove
public import Spqr.Specs.Chain.KeyHistory.Defs
import Spqr.Specs.Chain.DEFAULT_CHAIN_PARAMS
/-! # Spec theorem for `spqr::chain::{spqr::chain::KeyHistory}::gc`: loop body 0

One iteration of the garbage-collection loop. Given step size `i = 36`, the body inspects position
`i1` within `self.data` and produces a `ControlFlow`:

- **Done** (`i1 ≥ self.data.length`): returns the current `self.data` unchanged, certifying
  that the scan index has reached or passed the end.
- **Cont / Remove**
  (`i1 < self.data.length` and `lexCmpAux OrdU8 trim_horizon data[i1..i1+4] = ok .gt`,
  i.e. the 4-byte counter at `i1` is expired): produces `(self', i1)` where
  `self'.data.length = self.data.length - 36`, `i1` is unchanged and remains 36-aligned and
  in bounds of the shorter vector, `self'.data.length ≤ Usize.max`, bytes before `i1` are
  preserved element-wise, and the new data is either a swap-remove (`setSlice!` of the last
  36-byte record into position `i1`, then `take`) when the removed record is not the last, or
  a simple `take` truncation when `i1 + 36 = self.data.length`.
- **Cont / Advance** (`i1 < self.data.length` and the comparison is not `.gt`, i.e. the record
  is live): produces `(self, i1 + 36)` with `self` unchanged, `i1 + 36` 36-aligned,
  `i1 + 36 ≤ self.data.length`, and data length still 36-aligned and within `Usize.max`.

**Source**: spqr/src/chain.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.KeyHistory.gc_loop

/-- `Slice.lexCmpAux` instantiated with `OrdU8` is total: for any two byte lists `xs` and `ys`,
the comparison terminates with `ok o` for some `Ordering` `o`. Proved by induction on `xs`,
case-splitting on `ys` and the `compare` result on head elements. -/
private theorem lexCmpAux_OrdU8_ok (xs ys : List U8) :
    ∃ o, Slice.lexCmpAux core.cmp.OrdU8 xs ys = ok o := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨.eq, by unfold Slice.lexCmpAux; rfl⟩
    | cons _ _ => exact ⟨.lt, by unfold Slice.lexCmpAux; rfl⟩
  | cons a xs ih =>
    cases ys with
    | nil => exact ⟨.gt, by unfold Slice.lexCmpAux; rfl⟩
    | cons b ys =>
      unfold Slice.lexCmpAux
      simp only [core.cmp.OrdU8, liftFun2, core.cmp.impls.OrdU8.cmp]
      cases h : compare a.val b.val
      · exact ⟨.lt, by simp ⟩
      · simp only [bind_ok]
        exact ih ys
      · exact ⟨.gt, by simp⟩


/-- **Spec theorem for `spqr.chain.KeyHistory.gc_loop.body`**:

One step of the garbage-collection loop, producing a `ControlFlow` postcondition:

- **Done branch** (`¬(i1.val < self.data.length)`): the output equals `self.data` and the
  scan index has reached the end.
- **Cont branch** (`i1.val < self.data.length`): two sub-cases, distinguished by the
  lexicographic comparison of `trim_horizon` against the 4-byte slice at `i1`:
  - **Remove** (`lexCmpAux OrdU8 trim_horizon data[i1..i1+4] = ok .gt`): the returned
    `self'.data.length = self.data.length - 36`, the index `i1' = i1` (re-examine same
    position), `i1'` is 36-aligned and `≤ self'.data.length`, the new length fits in
    `Usize.max`, bytes before `i1` are element-wise preserved, and the resulting data is
    specified as either a swap-remove (`setSlice!` + `take`) when the record is interior, or
    a simple `take` truncation when `i1 + 36 = self.data.length`.
  - **Advance** (`lexCmpAux … ≠ ok .gt`): `self' = self` (unchanged), `i1'.val = i1.val + 36`,
    `i1'` is 36-aligned and `≤ self'.data.length`, and data length remains 36-aligned and
    within `Usize.max`. -/
@[step]
theorem body_spec
    (i : Usize) (params : proto.pq_ratchet.ChainParams)
    (trim_horizon : Slice U8) (self : chain.KeyHistory) (i1 : Usize)
    (h_i : i = 36#usize)
    (h_bound : self.data.length ≤ Usize.max)
    (h_aligned : i1.val % 36 = 0)
    (h_data_aligned : self.data.length % 36 = 0) :
    body i params trim_horizon self i1 ⦃ cf =>
      match cf with
      | ControlFlow.done out =>
          out = self.data ∧ ¬(i1.val < self.data.length)
      | ControlFlow.cont (self', i1') =>
          i1.val < self.data.length ∧
          (Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val
              (self.data.val.slice i1.val (i1.val + 4)) = ok .gt →
            self'.data.length = self.data.length - 36 ∧
            i1' = i1 ∧
            i1'.val % 36 = 0 ∧
            i1' ≤ self'.data.length ∧
            self'.data.length ≤ Usize.max ∧
            (∀ j, j < i1.val →
              self'.data[j]! = self.data[j]!) ∧
            (i1.val + 36 < self.data.length →
              self'.data =
                (self.data.val.setSlice! i1
                  (self.data.val.drop (self.data.length - 36))).take
                    (self.data.length - 36)) ∧
            (i1.val + 36 = self.data.length →
              self'.data = self.data.val.take i1)) ∧
          (Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val
              (self.data.val.slice i1.val (i1.val + 4)) ≠ ok .gt →
            self' = self ∧
            i1'.val = i1.val + 36 ∧
            i1'.val % 36 = 0 ∧
            i1'.val ≤ self'.data.length ∧
            self'.data.length ≤ Usize.max ∧
            self'.data.length % 36 = 0) ⦄ := by
  unfold body
  simp only [alloc.vec.Vec.len]
  split
  next h_lt =>
    have h_lt' : i1.val < self.data.length := by simpa using h_lt
    have h36 : i1.val + 36 ≤ self.data.length := by omega
    step as ⟨i3, h_i3⟩
    step as ⟨s, h_s, h_s_len⟩
    have hs : s.val = self.data.val.slice i1.val (i1.val + 4) := by rw [h_s, h_i3]
    simp only [Slice.Insts.CoreCmpOrd.cmp_eq, hs]
    by_cases hcmp : Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val
        (self.data.val.slice i1.val (i1.val + 4)) = ok .gt
    · -- the record at `i1` is expired: remove it
      rw [hcmp]
      simp only [bind_ok, if_true]
      step as ⟨self1, h_len, h_pre, h_sw, h_tr⟩
      refine ⟨h_lt', h_len, h_aligned, by omega, self1.data.property, ?_, h_sw, h_tr,
        fun h => absurd rfl h⟩
      intro j hj
      simpa [alloc.vec.Vec.getElem!_Nat_eq] using h_pre j hj
    · -- the record at `i1` is live: advance
      obtain ⟨o, ho⟩ :=
        lexCmpAux_OrdU8_ok trim_horizon.val (self.data.val.slice i1.val (i1.val + 4))
      have h_ngt : o ≠ .gt := fun h => hcmp (h ▸ ho)
      rw [ho, bind_ok]
      obtain rfl | rfl : o = .lt ∨ o = .eq := by cases o <;> simp_all
      all_goals
        dsimp only
        rw [bind_ok, if_neg Bool.false_ne_true]
        step as ⟨i4, h_i4⟩
        have h_i4' : i4.val = i1.val + 36 := by rw [h_i4, h_i]; rfl
        refine ⟨h_lt', fun h => ?_, fun _ => ⟨h_i4', by omega, by omega, h_bound, h_data_aligned⟩⟩
        cases h
  next h_ge =>
    rw [WP.spec_ok]
    exact ⟨rfl, by simpa using h_ge⟩


end spqr.chain.KeyHistory.gc_loop

/-!
**Spec theorem for `spqr::chain::{spqr::chain::KeyHistory}::gc`: loop 0**

Full fixed-point specification of the garbage-collection loop, proved by well-founded
recursion on the measure `self.data.length - i1.val` (which decreases by 36 on every
iteration—either via length shrinkage on remove, or index advancement).

**Preconditions** (mirrored as hypotheses):
- `i = 36` (step size)
- `self.data.length ≤ Usize.max`
- `i1.val % 36 = 0` and `self.data.length % 36 = 0`
- `i1.val ≤ self.data.length`

**Postconditions** on the returned `result : alloc.vec.Vec U8`:
1. `result.length % 36 = 0` — whole-record alignment preserved
2. `result.length ≤ Usize.max` — fits in platform word
3. `result.length ≤ self.data.length` — GC only removes, never grows
4. Prefix preservation: `∀ j < i1.val, result[j]! = self.data[j]!`
5. `i1.val ≤ result.length` — scan index still in bounds of result
6. Liveness: every 36-aligned record at position `m ≥ i1` in the result has
   `lexCmpAux OrdU8 trim_horizon result[m..m+4] ≠ ok .gt` (not expired)
7. Provenance: every record in result traces back to some record in `self.data`
   (existential witness with matching 36-byte slice)
8. Completeness: every unexpired record in `self.data` is retained in result
   (existential witness with matching 36-byte slice)
9. Injective forward map `f`: result records originate from distinct source records
   (no duplication)
10. Injective reverse map `g`: distinct unexpired source records map to distinct result
    records — together with (9), establishes a bijection between result records and
    unexpired source records

**Source**: spqr/src/chain.rs -/

namespace spqr.chain.KeyHistory

/-- Build a slice equality `a.slice m (m + len) = b.slice n (n + len)` from element-wise
`getElem!` equalities `∀ j < len, a[m + j]! = b[n + j]!`, given that both slices are
within bounds. -/
private theorem slice_eq_of_getElem! (a b : List U8) (m n len : Nat)
    (ha : m + len ≤ a.length) (hb : n + len ≤ b.length)
    (h : ∀ j, j < len → a[m + j]! = b[n + j]!) :
    a.slice m (m + len) = b.slice n (n + len) := by
  apply List.ext_getElem
  · simp [List.slice_length]; omega
  · intro j h1 h2
    simp only [List.slice_length] at h1
    have hj : j < len := by omega
    rw [List.getElem_slice _ _ _ _ ⟨by omega, by omega⟩,
        List.getElem_slice _ _ _ _ ⟨by omega, by omega⟩,
        List.Inhabited_getElem_eq_getElem! _ _ (by omega),
        List.Inhabited_getElem_eq_getElem! _ _ (by omega)]
    exact h j hj

/-- Extract element-wise `getElem!` equalities from a slice equality: if
`a.slice m (m + len) = b.slice n (n + len)` and both slices are in bounds, then
`∀ j < len, a[m + j]! = b[n + j]!`. Inverse of `slice_eq_of_getElem!`. -/
private theorem getElem!_of_slice_eq (a b : List U8) (m n len : Nat)
    (h : a.slice m (m + len) = b.slice n (n + len))
    (ha : m + len ≤ a.length) (hb : n + len ≤ b.length)
    (j : Nat) (hj : j < len) :
    a[m + j]! = b[n + j]! := by
  have h1 : (a.slice m (m + len))[j]! = a[m + j]! := by
    rw [List.getElem!_slice _ _ _ _ ⟨by omega, by omega⟩]
  have h2 : (b.slice n (n + len))[j]! = b[n + j]! := by
    rw [List.getElem!_slice _ _ _ _ ⟨by omega, by omega⟩]
  rw [← h1, ← h2, h]

private theorem slice_eq_of_prefix (a b : List U8) (m : Nat)
    (ha : m + 4 ≤ a.length) (hb : m + 4 ≤ b.length)
    (h : ∀ j, j < m + 4 → a[j]! = b[j]!) :
    a.slice m (m + 4) = b.slice m (m + 4) := by
  apply List.ext_getElem
  · simp only [List.slice_length]; omega
  · intro n h1 h2
    have hn : n < 4 := by simp only [List.slice_length] at h1; omega
    rw [List.getElem_slice m (m + 4) n a (by omega),
        List.getElem_slice m (m + 4) n b (by omega),
        List.Inhabited_getElem_eq_getElem! a (m + n) (by omega),
        List.Inhabited_getElem_eq_getElem! b (m + n) (by omega)]
    exact h (m + n) (by omega)

/-- If `a < b` and both are 36-aligned, then `a + 36 ≤ b`. -/
private theorem aligned36_step {a b : Nat} (ha : a % 36 = 0) (hb : b % 36 = 0) (h : a < b) :
    a + 36 ≤ b := by
  have := Nat.div_add_mod a 36; have := Nat.div_add_mod b 36; omega

/-- If a 36-byte record at position `p` in `a` equals the record at position `n` in `b`,
then the 4-byte timestamp prefixes also match. -/
private theorem timestamp_of_record_eq (a b : List U8) (p n : Nat)
    (heq : a.slice p (p + 36) = b.slice n (n + 36))
    (ha : p + 36 ≤ a.length) (hb : n + 36 ≤ b.length) :
    a.slice p (p + 4) = b.slice n (n + 4) := by
  apply slice_eq_of_getElem! _ _ _ _ 4 (by omega) (by omega)
  intro j hj
  exact getElem!_of_slice_eq _ _ _ _ 36 heq ha hb j (by omega)

/-- If the record at `k` in `s` has the same timestamp as record `n` in `orig`, and
`k` is expired, then `n` cannot be unexpired—contradiction yielding `False`. -/
private theorem expired_contradicts_live
    (s_data orig_data : List U8) (k n : Nat)
    (trim_horizon : List U8)
    (heq : s_data.slice k (k + 36) = orig_data.slice n (n + 36))
    (hk_bnd : k + 36 ≤ s_data.length) (hn_bnd : n + 36 ≤ orig_data.length)
    (hcmp : Slice.lexCmpAux core.cmp.OrdU8 trim_horizon
        (s_data.slice k (k + 4)) = ok .gt)
    (hn_live : Slice.lexCmpAux core.cmp.OrdU8 trim_horizon
        (orig_data.slice n (n + 4)) ≠ ok .gt) :
    False := by
  rw [timestamp_of_record_eq s_data orig_data k n heq hk_bnd hn_bnd] at hcmp
  exact absurd hcmp hn_live


/-- Read element `k + j` from the swap position: it equals the last record's
element `data[data.length - 36 + j]`. -/
private theorem getElem!_swap_at_k (data s'_data : List U8) (k j : Nat)
    (hlen_al : data.length % 36 = 0)
    (hk_al : k % 36 = 0) (hk_swap : k + 36 < data.length)
    (hj : j < 36)
    (hsw_eq : s'_data = (data.setSlice! k (data.drop (data.length - 36))).take
        (data.length - 36)) :
    s'_data[k + j]! = data[data.length - 36 + j]! := by
  rw [hsw_eq, List.getElem!_take_of_lt _ _ _ (by omega),
      List.getElem!_setSlice!_middle _ _ _ _
        ⟨by omega,
         by simp [List.length_drop]; omega,
         by omega⟩,
      List.getElem!_drop]
  congr 1; omega

/-- After a swap-remove at position `k`, any record at `m ≠ k` reads the same as in `s`. -/
private theorem getElem!_record_preserved_nonswap
    (s_data s'_data : List U8) (k m : Nat)
    (hs_al : s_data.length % 36 = 0)
    (hk_al : k % 36 = 0) (hm_al : m % 36 = 0)
    (hm_ne_k : m ≠ k) (hm_lt_s : m < s_data.length)
    (hlen : s'_data.length = s_data.length - 36)
    (hk_bnd : k + 36 ≤ s_data.length)
    (hm_lt_s' : m < s'_data.length)
    (hsw : k + 36 < s_data.length →
      s'_data = (s_data.setSlice! k (s_data.drop (s_data.length - 36))).take
        (s_data.length - 36))
    (htr : k + 36 = s_data.length → s'_data = s_data.take k) :
    ∀ j, j < 36 → s'_data[m + j]! = s_data[m + j]! := by
  intro j hj
  by_cases hmk2 : k + 36 < s_data.length
  · have hsw' := hsw hmk2
    by_cases hm_before_k : m + 36 ≤ k
    · rw [hsw', List.getElem!_take_of_lt _ _ _ (by omega),
          List.getElem!_setSlice!_prefix _ _ _ _ (by omega)]
    · have : k + 36 ≤ m := by omega
      rw [hsw', List.getElem!_take_of_lt _ _ _ (by omega),
          List.getElem!_setSlice!_suffix _ _ _ _
            (by simp [List.length_drop]; omega)]
  · have hk36 : k + 36 = s_data.length := by omega
    rw [htr hk36, List.getElem!_take_of_lt _ _ _ (by omega)]

/-- After a swap-remove at `k`, the 36-byte record at position `m` in the shorter array
equals the record at position `src` in the original array, where `src = len - 36` when
`m = k` and a swap occurred, and `src = m` otherwise. -/
private theorem record_at_after_remove
    (s_data s'_data : List U8) (k m : Nat)
    (hs_al : s_data.length % 36 = 0) (hk_al : k % 36 = 0) (hm_al : m % 36 = 0)
    (hm_lt_s' : m < s'_data.length)
    (hlen : s'_data.length = s_data.length - 36)
    (hk_bnd : k + 36 ≤ s_data.length)
    (hsw : k + 36 < s_data.length →
      s'_data = (s_data.setSlice! k (s_data.drop (s_data.length - 36))).take
        (s_data.length - 36))
    (htr : k + 36 = s_data.length → s'_data = s_data.take k) :
    let src := if m = k ∧ k + 36 < s_data.length then s_data.length - 36 else m
    src < s_data.length ∧ src % 36 = 0 ∧
    s'_data.slice m (m + 36) = s_data.slice src (src + 36) := by
  simp only
  split
  · next h =>
    obtain ⟨hmeq, hswap⟩ := h
    subst hmeq -- eliminates k, replacing with m
    refine ⟨by omega, by omega, ?_⟩
    apply slice_eq_of_getElem! _ _ _ _ 36 (by omega) (by omega)
    intro j hj
    exact getElem!_swap_at_k s_data s'_data m j hs_al hk_al hswap hj (hsw hswap)
  · next h =>
    have hm_lt_s : m < s_data.length := by omega
    refine ⟨hm_lt_s, hm_al, ?_⟩
    have hm_ne_k : m ≠ k := by
      intro heq; subst heq
      exact h ⟨rfl, by omega⟩
    apply slice_eq_of_getElem! _ _ _ _ 36 (by omega) (by omega)
    exact getElem!_record_preserved_nonswap s_data s'_data k m
      hs_al hk_al hm_al hm_ne_k hm_lt_s hlen hk_bnd hm_lt_s' hsw htr

/-- After a swap-remove at `k`, given a record at `m` in the old array (`m ≠ k`),
find its position in the shorter array. If `m` was the last record and a swap happened,
it moved to `k`; otherwise it stayed at `m`. -/
private theorem completeness_through_remove
    (s_data s'_data : List U8) (k m : Nat)
    (hs_al : s_data.length % 36 = 0) (hk_al : k % 36 = 0) (hm_al : m % 36 = 0)
    (hm_ne_k : m ≠ k) (hm_lt_s : m < s_data.length)
    (hlen : s'_data.length = s_data.length - 36)
    (hk_bnd : k + 36 ≤ s_data.length)
    (hsw : k + 36 < s_data.length →
      s'_data = (s_data.setSlice! k (s_data.drop (s_data.length - 36))).take
        (s_data.length - 36))
    (htr : k + 36 = s_data.length → s'_data = s_data.take k) :
    ∃ m', m' < s'_data.length ∧ m' % 36 = 0 ∧
      s'_data.slice m' (m' + 36) = s_data.slice m (m + 36) := by
  by_cases hmk_last : m = s_data.length - 36
  · have hmk2 : k + 36 < s_data.length := by
      have : m + 36 ≤ s_data.length := by
        have := Nat.div_add_mod m 36; have := Nat.div_add_mod s_data.length 36; omega
      omega
    refine ⟨k, by (rw [hlen]; omega), hk_al, ?_⟩
    have ⟨_, _, heq⟩ := record_at_after_remove s_data s'_data k k hs_al hk_al hk_al
      (by rw [hlen]; omega) hlen hk_bnd hsw htr
    simp only [and_self, ite_true, hmk2] at heq
    rw [heq, hmk_last]
  · have hm_lt' : m < s'_data.length := by
      rw [hlen]
      have := Nat.div_add_mod m 36; have := Nat.div_add_mod s_data.length 36; omega
    refine ⟨m, hm_lt', hm_al, ?_⟩
    have ⟨_, _, heq⟩ := record_at_after_remove s_data s'_data k m hs_al hk_al hm_al
      hm_lt' hlen hk_bnd hsw htr
    have : ¬(m = k ∧ k + 36 < s_data.length) := fun ⟨h, _⟩ => hm_ne_k h
    simp only [this, ite_false] at heq
    exact heq

private theorem subseq_after_remove
    (s_data s'_data orig_data : List U8) (k m : Nat)
    (hs_al : s_data.length % 36 = 0) (hk_al : k % 36 = 0) (hm_al : m % 36 = 0)
    (hm_lt_s' : m < s'_data.length)
    (hlen : s'_data.length = s_data.length - 36)
    (hk_bnd : k + 36 ≤ s_data.length)
    (hsw : k + 36 < s_data.length →
      s'_data = (s_data.setSlice! k (s_data.drop (s_data.length - 36))).take
        (s_data.length - 36))
    (htr : k + 36 = s_data.length → s'_data = s_data.take k)
    (hsubseq : ∀ p, p < s_data.length ∧ p % 36 = 0 →
      ∃ n, n < orig_data.length ∧ n % 36 = 0 ∧
        s_data.slice p (p + 36) = orig_data.slice n (n + 36)) :
    ∃ n, n < orig_data.length ∧ n % 36 = 0 ∧
      s'_data.slice m (m + 36) = orig_data.slice n (n + 36) := by
  have hm_lt_s : m < s_data.length := by omega
  have ⟨hsrc_lt, hsrc_al, hsrc_eq⟩ := record_at_after_remove s_data s'_data k m
    hs_al hk_al hm_al hm_lt_s' hlen hk_bnd hsw htr
  let src := if m = k ∧ k + 36 < s_data.length then s_data.length - 36 else m
  obtain ⟨n, hn1, hn2, hn3⟩ := hsubseq src ⟨hsrc_lt, hsrc_al⟩
  exact ⟨n, hn1, hn2, hsrc_eq.trans hn3⟩


/-- Loop invariant of `gc_loop`, for the state `(s, k)` (current history and scan index). -/
private structure GcLoopInv (self : chain.KeyHistory) (trim_horizon : Slice U8) (i1 : Usize)
    (s : chain.KeyHistory) (k : Usize) : Prop where
  k_al : k.val % 36 = 0
  s_al : s.data.length % 36 = 0
  s_bnd : s.data.length ≤ Usize.max
  k_le : k.val ≤ s.data.length
  s_le : s.data.length ≤ self.data.length
  mono : i1.val ≤ k.val
  pres : ∀ j, j < i1.val → s.data.val[j]! = self.data.val[j]!
  /-- every record already scanned (in `[i1, k)`) is live -/
  live : ∀ m, i1.val ≤ m ∧ m < k.val ∧ m % 36 = 0 →
    Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val (s.data.val.slice m (m + 4)) ≠ ok .gt
  /-- every record of `s` comes from `self` -/
  subseq : ∀ m, m < s.data.length ∧ m % 36 = 0 →
    ∃ n, n < self.data.length ∧ n % 36 = 0 ∧
      s.data.val.slice m (m + 36) = self.data.val.slice n (n + 36)
  /-- every unexpired record of `self` is retained -/
  complete : ∀ n, n < self.data.length ∧ n % 36 = 0 →
    Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val (self.data.val.slice n (n + 4)) ≠ ok .gt →
    ∃ m, m < s.data.length ∧ m % 36 = 0 ∧
      s.data.val.slice m (m + 36) = self.data.val.slice n (n + 36)
  /-- injective provenance map from records of `s` to records of `self` -/
  fwd : ∃ f : Nat → Nat,
    (∀ m, m < s.data.length ∧ m % 36 = 0 →
      f m < self.data.length ∧ (f m) % 36 = 0 ∧
      s.data.val.slice m (m + 36) = self.data.val.slice (f m) (f m + 36)) ∧
    (∀ m₁ m₂, m₁ < s.data.length ∧ m₁ % 36 = 0 → m₂ < s.data.length ∧ m₂ % 36 = 0 →
      f m₁ = f m₂ → m₁ = m₂)
  /-- injective map from unexpired records of `self` to records of `s` -/
  bwd : ∃ g : Nat → Nat,
    (∀ n, n < self.data.length ∧ n % 36 = 0 →
      Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val (self.data.val.slice n (n + 4)) ≠ ok .gt →
      g n < s.data.length ∧ (g n) % 36 = 0 ∧
      s.data.val.slice (g n) (g n + 36) = self.data.val.slice n (n + 36)) ∧
    (∀ n₁ n₂, n₁ < self.data.length ∧ n₁ % 36 = 0 → n₂ < self.data.length ∧ n₂ % 36 = 0 →
      Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val (self.data.val.slice n₁ (n₁ + 4)) ≠ ok .gt →
      Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val (self.data.val.slice n₂ (n₂ + 4)) ≠ ok .gt →
      g n₁ = g n₂ → n₁ = n₂)

/-- **Spec theorem for `spqr.chain.KeyHistory.gc_loop`**:

Applies `loop.spec_decr_nat` with measure `self.data.length - i1.val` and the loop-body
spec `body_spec` to derive the full postcondition of the GC loop. The result `Vec U8`
satisfies all ten properties enumerated in the section-level docstring: 36-alignment,
`Usize.max` bound, monotonic shrinkage, prefix preservation, scan-index bound, liveness of
all records past `i1`, provenance/completeness with injective forward and reverse mappings. -/
@[step]
theorem gc_loop_spec
    (i : Usize) (self : chain.KeyHistory)
    (params : proto.pq_ratchet.ChainParams)
    (trim_horizon : Slice U8) (i1 : Usize)
    (h_i : i = 36#usize)
    (h_bound : self.data.length ≤ Usize.max)
    (h_aligned : i1.val % 36 = 0)
    (h_data_aligned : self.data.length % 36 = 0)
    (h_i1_bound : i1.val ≤ self.data.length) :
    gc_loop i self params trim_horizon i1 ⦃ (result : alloc.vec.Vec U8) =>
      GcLoopPost self trim_horizon i1 result ⦄ := by
  unfold GcLoopPost
  unfold gc_loop
  apply loop.spec_decr_nat
    (measure := fun (p : chain.KeyHistory × Usize) => p.1.data.length - p.2.val)
    (inv := fun p => GcLoopInv self trim_horizon i1 p.1 p.2)
  · rintro ⟨s, k⟩ (hinv : GcLoopInv self trim_horizon i1 s k)
    obtain ⟨hk_al, hs_al, hs_bnd, hkb, hs_le, hmono, hpres, hlive, hsubseq, hcomplete,
      ⟨f_inv, hf_prov, hf_inj⟩, ⟨g_inv, hg_prov, hg_inj⟩⟩ := hinv
    have hs_vl : s.data.val.length = s.data.length := rfl
    have hself_vl : self.data.val.length = self.data.length := rfl
    have hspec := gc_loop.body_spec i params trim_horizon s k h_i hs_bnd hk_al hs_al
    apply WP.spec_mono hspec
    intro cf hcf
    rcases cf with ⟨s', k'⟩ | out <;> dsimp only at hcf ⊢
    · obtain ⟨hlt, hrem, hadv⟩ := hcf
      by_cases hcmp : Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val
          (s.data.val.slice k.val (k.val + 4)) = ok .gt
      · obtain ⟨hlen, hkeq, hal, hib, hbnd', hpre, hsw, htr⟩ := hrem hcmp
        have hk36_bnd : k.val + 36 ≤ s.data.length :=
          aligned36_step hk_al hs_al (by omega)
        -- the length facts in the list-level form used by the record lemmas
        have hsL_al : s.data.val.length % 36 = 0 := hs_al
        have hlenL : s'.data.val.length = s.data.val.length - 36 := hlen
        have hkL : k.val + 36 ≤ s.data.val.length := hk36_bnd
        have hlast_lt : s.data.length - 36 < s.data.length := by omega
        have hlast_al : (s.data.length - 36) % 36 = 0 := by omega
        have h_lt_s : ∀ m, m < s'.data.length → m < s.data.length := fun m h => by omega
        refine ⟨⟨hal, ?_, hbnd', hib, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · rw [hlen]
          omega
        · rw [hlen]
          omega
        · rw [hkeq]
          exact hmono
        · intro j hj
          have hjk : j < k.val := lt_of_lt_of_le hj hmono
          have h1 := hpre j hjk
          have h2 := hpres j hj
          exact h1.trans h2
        · intro m hm1 hm2
          rw [hkeq] at hm1
          have hm4 : m + 4 ≤ k.val := by omega
          have hibk : k.val ≤ s'.data.length := by rw [hkeq] at hib; exact hib
          have hsl : s'.data.val.slice m (m + 4) = s.data.val.slice m (m + 4) := by
            apply slice_eq_of_prefix
            · exact le_trans hm4 hibk
            · exact le_trans hm4 hkb
            · intro j hj
              exact hpre j (by omega)
          rw [hsl] at hm2
          exact hlive m ⟨hm1.1, hm1.2.1, hm1.2.2⟩ hm2
        · intro m ⟨hml, hmal⟩
          exact subseq_after_remove s.data.val s'.data.val self.data.val k.val m
            hsL_al hk_al hmal hml hlenL hkL hsw htr
            (fun p hp => hsubseq p hp)
        · intro n ⟨hn_lt, hn_al⟩ hn_live
          obtain ⟨m, hm_lt, hm_al, hm_eq⟩ := hcomplete n ⟨hn_lt, hn_al⟩ hn_live
          by_cases hmk_eq : m = k.val
          · subst hmk_eq
            exact absurd hcmp (by
              rw [timestamp_of_record_eq _ _ _ _ hm_eq
                (by omega)
                (by omega)]
              exact hn_live)
          · obtain ⟨m', hm'_lt, hm'_al, hm'_eq⟩ := completeness_through_remove
              s.data.val s'.data.val k.val m
              hsL_al hk_al hm_al hmk_eq hm_lt hlenL hkL hsw htr
            exact ⟨m', hm'_lt, hm'_al, hm'_eq.trans hm_eq⟩
        · let src := fun m => if m = k.val ∧ k.val + 36 < s.data.length
            then s.data.length - 36 else m
          let f' : Nat → Nat := fun m => f_inv (src m)
          refine ⟨f', fun m ⟨hml, hmal⟩ => ?_, fun m₁ m₂ ⟨hm1l, hm1a⟩ ⟨hm2l, hm2a⟩ hfeq => ?_⟩
          · have ⟨hsrc_lt, hsrc_al, hsrc_eq⟩ := record_at_after_remove
              s.data.val s'.data.val k.val m hsL_al hk_al hmal hml hlenL hkL hsw htr
            have ⟨hf1, hf2, hf3⟩ := hf_prov (src m) ⟨hsrc_lt, hsrc_al⟩
            exact ⟨hf1, hf2, hsrc_eq.trans hf3⟩
          · show m₁ = m₂
            simp only [f', src] at hfeq
            by_cases h1 : m₁ = k.val ∧ k.val + 36 < s.data.length <;>
            by_cases h2 : m₂ = k.val ∧ k.val + 36 < s.data.length
            · exact h1.1.trans h2.1.symm
            · have hfeq' : f_inv (s.data.length - 36) = f_inv m₂ := by
                rw [if_pos h1, if_neg h2] at hfeq; exact hfeq
              have := hf_inj (s.data.length - 36) m₂
                ⟨hlast_lt, hlast_al⟩ ⟨h_lt_s _ hm2l, hm2a⟩ hfeq'
              rw [hlen] at hm2l; omega
            · have hfeq' : f_inv m₁ = f_inv (s.data.length - 36) := by
                rw [if_neg h1, if_pos h2] at hfeq; exact hfeq
              have := hf_inj m₁ (s.data.length - 36)
                ⟨h_lt_s _ hm1l, hm1a⟩ ⟨hlast_lt, hlast_al⟩ hfeq'
              rw [hlen] at hm1l; omega
            · exact hf_inj m₁ m₂ ⟨h_lt_s _ hm1l, hm1a⟩ ⟨h_lt_s _ hm2l, hm2a⟩
                (by rw [if_neg h1, if_neg h2] at hfeq; exact hfeq)
        · let dst := fun n => if g_inv n = s.data.length - 36 ∧ k.val + 36 < s.data.length
            then k.val else g_inv n
          let g' : Nat → Nat := dst
          refine ⟨g', fun n ⟨hn_lt, hn_al⟩ hn_live => ?_,
            fun n₁ n₂ ⟨hn1_lt, hn1_al⟩ ⟨hn2_lt, hn2_al⟩ hn1_live hn2_live hgeq => ?_⟩
          · obtain ⟨hgn_lt, hgn_al, hgn_eq⟩ := hg_prov n ⟨hn_lt, hn_al⟩ hn_live
            have hgn_ne_k : g_inv n ≠ k.val := by
              intro heq; rw [← heq] at hcmp
              exact expired_contradicts_live _ _ _ _ _ hgn_eq
                (by omega) (by omega) hcmp hn_live
            obtain ⟨m', hm'_lt, hm'_al, hm'_eq⟩ := completeness_through_remove
              s.data.val s'.data.val k.val (g_inv n)
              hsL_al hk_al hgn_al hgn_ne_k hgn_lt hlenL hkL hsw htr
            simp only [g', dst]
            by_cases hg_last_swap : g_inv n = s.data.length - 36 ∧ k.val + 36 < s.data.length
            · simp only [hg_last_swap]
              have ⟨_, _, hk_eq⟩ := record_at_after_remove s.data.val s'.data.val k.val k.val
                hsL_al hk_al hk_al (by omega) hlenL hkL hsw htr
              simp only [and_self, hg_last_swap.2, ite_true] at hk_eq
              rw [hg_last_swap.1] at hgn_eq
              have hswap : k.val + 36 < s.data.length := hg_last_swap.2
              refine ⟨?_, hk_al, hk_eq.trans hgn_eq⟩
              simp [alloc.vec.Vec.length] at hlen hswap ⊢; omega
            · simp only [hg_last_swap, ite_false]
              have : ¬(g_inv n = s.data.length - 36 ∧ k.val + 36 < s.data.length) := hg_last_swap
              have hgn_lt' : g_inv n < s'.data.length := by
                -- `g_inv n` is not the last record: if it were, no swap happened (`k` was the
                -- last record), so `g_inv n = k`, which is expired
                have h36 : g_inv n + 36 ≤ s.data.length := aligned36_step hgn_al hs_al hgn_lt
                have hne : g_inv n ≠ s.data.length - 36 := fun heq_last =>
                  hg_last_swap ⟨heq_last, by omega⟩
                rw [hlen]
                omega
              refine ⟨hgn_lt', hgn_al, ?_⟩
              have ⟨_, _, hsrc_eq⟩ := record_at_after_remove
                s.data.val s'.data.val k.val (g_inv n)
                hsL_al hk_al hgn_al hgn_lt' hlenL hkL hsw htr
              have : ¬(g_inv n = k.val ∧ k.val + 36 < s.data.length) := by
                intro ⟨h, _⟩; exact hgn_ne_k h
              simp only [this, ite_false] at hsrc_eq
              exact hsrc_eq.trans hgn_eq
          · show n₁ = n₂
            simp only [g', dst] at hgeq
            have g_ne_k : ∀ ni, ni < self.data.length → ni % 36 = 0 →
                Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val
                  (self.data.val.slice ni (ni + 4)) ≠ ok .gt →
                g_inv ni ≠ k.val := by
              intro ni hni_lt hni_al hni_live heq
              obtain ⟨_, _, hgni_eq⟩ := hg_prov ni ⟨hni_lt, hni_al⟩ hni_live
              rw [← heq] at hcmp
              exact expired_contradicts_live _ _ _ _ _ hgni_eq
                (by omega) (by omega) hcmp hni_live
            by_cases h1 : g_inv n₁ = s.data.length - 36 ∧ k.val + 36 < s.data.length <;>
            by_cases h2 : g_inv n₂ = s.data.length - 36 ∧ k.val + 36 < s.data.length
            · exact hg_inj n₁ n₂ ⟨hn1_lt, hn1_al⟩ ⟨hn2_lt, hn2_al⟩ hn1_live hn2_live
                (by rw [h1.1, h2.1])
            · rw [if_pos h1, if_neg h2] at hgeq
              exact (g_ne_k n₂ hn2_lt hn2_al hn2_live hgeq.symm).elim
            · rw [if_neg h1, if_pos h2] at hgeq
              exact (g_ne_k n₁ hn1_lt hn1_al hn1_live hgeq).elim
            · rw [if_neg h1, if_neg h2] at hgeq
              exact hg_inj n₁ n₂ ⟨hn1_lt, hn1_al⟩ ⟨hn2_lt, hn2_al⟩ hn1_live hn2_live hgeq
        · rw [hkeq] at hib ⊢; rw [hlen] at hib ⊢; omega
      · obtain ⟨hself, hkeq, hal, hib, _hbnd, _hal2⟩ := hadv hcmp
        subst hself
        refine ⟨⟨hal, hs_al, hs_bnd, hib, hs_le, ?_, hpres, ?_, hsubseq, hcomplete,
          ⟨f_inv, hf_prov, hf_inj⟩, ⟨g_inv, hg_prov, hg_inj⟩⟩, ?_⟩
        · omega
        · intro m hm1 hm2
          by_cases hmk : m < k.val
          · exact hlive m ⟨hm1.1, hmk, hm1.2.2⟩ hm2
          · have hmeq : m = k.val := by omega
            subst hmeq; exact hcmp hm2
        · omega
    · obtain ⟨hout, _hnlt⟩ := hcf
      subst hout
      refine ⟨hs_al, hs_bnd, hs_le, hpres, le_trans hmono hkb, ?_, ?_, ?_, ?_, ?_⟩
      · intro m ⟨hm1, hm2, hm3⟩
        have : m < k.val := by omega
        exact hlive m ⟨hm1, this, hm3⟩
      · intro m hm
        obtain ⟨n, hn1, hn2, hn3⟩ := hsubseq m hm
        exact ⟨n, ⟨hn1, hn2⟩, hn3⟩
      · intro n hn hn_live
        obtain ⟨m, hm1, hm2, hm3⟩ := hcomplete n hn hn_live
        exact ⟨m, ⟨hm1, hm2⟩, hm3⟩
      · exact ⟨f_inv, fun m hm => let ⟨a, b, c⟩ := hf_prov m hm; ⟨⟨a, b⟩, c⟩, hf_inj⟩
      · exact ⟨g_inv, fun n hn hlive => let ⟨a, b, c⟩ := hg_prov n hn hlive; ⟨⟨a, b⟩, c⟩, hg_inj⟩
  · dsimp only
    exact ⟨h_aligned, h_data_aligned, h_bound, h_i1_bound, le_refl _, le_refl _,
      fun j _ => rfl, fun m h => by omega,
      fun m ⟨hml, hmal⟩ => ⟨m, hml, hmal, rfl⟩,
      fun n ⟨hn_lt, hn_al⟩ _ => ⟨n, hn_lt, hn_al, rfl⟩,
      ⟨fun m => m, fun m ⟨hml, hmal⟩ => ⟨hml, hmal, rfl⟩,
       fun _ _ _ _ h => h⟩,
      ⟨fun n => n, fun n ⟨hn_lt, hn_al⟩ _ => ⟨hn_lt, hn_al, rfl⟩,
       fun _ _ _ _ _ _ h => h⟩⟩




/-! ### `gc` -/

/-- Value-level spec of `max_ooo_keys_or_default`. -/
private theorem max_ooo_keys_or_default_val (params : proto.pq_ratchet.ChainParams) :
    chain.ChainParams.max_ooo_keys_or_default params ⦃ (r : U32) =>
      r.val = if 0#u32 < params.max_ooo_keys then params.max_ooo_keys.val else 2000 ⦄ := by
  unfold chain.ChainParams.max_ooo_keys_or_default
  split <;> simp_all [DEFAULT_CHAIN_PARAMS_spec]

/-- Value-level spec of `trim_size`. -/
private theorem trim_size_val (params : proto.pq_ratchet.ChainParams)
    (h_ooo : params.max_ooo_keys.val < 390451572) :
    chain.ChainParams.trim_size params ⦃ (r : Usize) =>
      r.val = (if 0#u32 < params.max_ooo_keys then params.max_ooo_keys.val else 2000) * 11 / 10
        + 1 ⦄ := by
  unfold chain.ChainParams.trim_size
  step with max_ooo_keys_or_default_val as ⟨i, h_i⟩
  have : i.val < 390451572 := by rw [h_i]; split <;> omega
  step*

/-- `GcPost` when `gc` does nothing (the history is below the trim threshold). -/
private theorem gcPost_noop (self : chain.KeyHistory) (current_key : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_aligned : self.data.length % 36 = 0)
    (h_lt : self.data.length <
      ((if 0#u32 < params.max_ooo_keys then params.max_ooo_keys.val else 2000) * 11 / 10 + 1)
        * 36) :
    GcPost self current_key params self :=
  ⟨h_aligned, le_refl _, fun _ => rfl, fun h => absurd h (by omega)⟩

/-- `GcPost` from the loop postcondition, when `gc` scans the history with the horizon
`i5 = current_key - max_ooo`. -/
private theorem gcPost_of_loopPost (self : chain.KeyHistory) (current_key : U32)
    (params : proto.pq_ratchet.ChainParams) (i5 : U32) (a : Std.Array U8 4#usize)
    (v : alloc.vec.Vec U8)
    (h_ge : ((if 0#u32 < params.max_ooo_keys then params.max_ooo_keys.val else 2000) * 11 / 10
      + 1) * 36 ≤ self.data.length)
    (h_i5 : i5.val = current_key.val -
      (if 0#u32 < params.max_ooo_keys then params.max_ooo_keys.val else 2000))
    (h_a : a.val = horizonBytes i5)
    (h_v : GcLoopPost self a.to_slice 0#usize v) :
    GcPost self current_key params { data := v } := by
  obtain ⟨hv1, -, hv3, -, -, hv6, -, hv8, ⟨f_inv, hv9, hv10⟩, ⟨g_inv, hv11, hv12⟩⟩ := h_v
  have h_th : (a.to_slice).val = (horizonSlice i5).val := by simp [Array.val_to_slice, h_a]
  refine ⟨hv1, hv3, fun h_lt => absurd h_ge (by omega), fun _ => ⟨i5, h_i5, ?_, ?_, ?_, ?_⟩⟩
  · intro m hm
    have := hv6 m ⟨Nat.zero_le _, hm⟩
    simpa [IsExpired, h_th] using this
  · intro n hn hn_live
    obtain ⟨m, hm⟩ := hv8 n hn (by simpa [IsExpired, h_th] using hn_live)
    exact ⟨m, hm⟩
  · exact ⟨f_inv, hv9, hv10⟩
  · refine ⟨g_inv, fun n hn hn_live => hv11 n hn (by simpa [IsExpired, h_th] using hn_live),
      fun n₁ n₂ h1 h2 hl1 hl2 => hv12 n₁ n₂ h1 h2 (by simpa [IsExpired, h_th] using hl1)
        (by simpa [IsExpired, h_th] using hl2)⟩

private theorem gc_spec_core (self : chain.KeyHistory) (current_key : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_bound : self.data.length ≤ Usize.max)
    (h_data_aligned : self.data.length % 36 = 0)
    (h_ooo : params.max_ooo_keys.val < 390451572)
    (h_fit : (params.max_ooo_keys.val * 11 / 10 + 1) * 36 ≤ Usize.max)
    (h_key_ge : let max_ooo := if 0#u32 < params.max_ooo_keys then params.max_ooo_keys.val else 2000
                let trim_threshold := (max_ooo * 11 / 10 + 1) * 36
                trim_threshold ≤ self.data.length → max_ooo ≤ current_key.val) :
    gc self current_key params ⦃ (result : chain.KeyHistory) =>
      GcPost self current_key params result ⦄ := by
  unfold gc
  simp only [alloc.vec.Vec.len]
  step with trim_size_val as ⟨i1, h_i1⟩
  step as ⟨i2, h_i2⟩
  subst h_i2
  have : i1.val * (36#usize).val ≤ Usize.max := by
    rw [h_i1]; split
    · exact h_fit
    · scalar_tac
  step as ⟨i3, h_i3⟩
  split
  next hge =>
    have hge' : i3.val ≤ self.data.length := hge
    step with max_ooo_keys_or_default_val as ⟨i4, h_i4⟩
    have : i4.val ≤ current_key.val := by rw [h_i4]; exact h_key_ge (by rw [← h_i1]; omega)
    step
    step as ⟨i5, h_i5, _⟩
    step as ⟨a, h_a⟩
    step as ⟨v, h_v⟩
    exact gcPost_of_loopPost self current_key params i5 a v (by rw [← h_i1]; omega)
      (by rw [h_i5, h_i4]) h_a h_v
  next hlt =>
    have hlt' : self.data.length < i3.val := by simpa using hlt
    rw [WP.spec_ok]
    exact gcPost_noop self current_key params h_data_aligned (by rw [← h_i1]; omega)

/-!**Spec theorem for `spqr::chain::{spqr::chain::KeyHistory}::gc` (32-bit platform)**

32-bit and 64-bit variant of `gc_spec` (proved in `Gc.lean`). Differences from 64-bit:
- `h_ooo : params.max_ooo_keys.val < 108458770` (tighter bound ensuring `trim_size * KEY_SIZE`
fits in 32-bit `usize` and so it also fits in 64-bit `usize` )

**Rationale for tighter bound**:
- `max_ooo_keys < 108458770` → `trim_size * 36 ≤ 4294967295` (`U32.max`)
- 64-bit bound (`390451572`) would yield `trim_threshold ≈ 15.4B`, overflowing 32-bit `usize`

**Source**: spqr/src/chain.rs-/
@[step]
theorem gc_spec (self : chain.KeyHistory) (current_key : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_bound : self.data.length ≤ Usize.max)
    (h_data_aligned : self.data.length % 36 = 0)
    (h_ooo : params.max_ooo_keys.val < 108458770)
    (h_key_ge : let max_ooo := if 0#u32 < params.max_ooo_keys then params.max_ooo_keys.val else 2000
                let trim_threshold := (max_ooo * 11 / 10 + 1) * 36
                trim_threshold ≤ self.data.length → max_ooo ≤ current_key.val) :
    gc self current_key params ⦃ (result : chain.KeyHistory) =>
      GcPost self current_key params result ⦄ := by
  exact gc_spec_core self current_key params h_bound h_data_aligned (by omega)
    (by scalar_tac) h_key_ge


/-- **Spec theorem for `spqr.chain.KeyHistory.gc`** (64-bit platform):

Top-level GC entry point. Computes `max_ooo` (from `params.max_ooo_keys` or default 2000),
`trim_size = max_ooo * 11 / 10 + 1`, and `trim_threshold = trim_size * 36`. Then:

- **(1) Alignment**: `result.data.length % 36 = 0`
- **(2) Shrinkage**: `result.data.length ≤ self.data.length`
- **(3) No-op below threshold**: `self.data.length < trim_threshold → result = self`
- **(4) Above threshold**: `trim_threshold ≤ self.data.length →` there exists a `horizon : U32`
  with `horizon.val = current_key.val - max_ooo`, and:
  - **(4a)** horizon value as stated
  - **(4b)** liveness: every 36-aligned record in the result is unexpired w.r.t. `horizon`
  - **(4c)** completeness: every unexpired record in `self.data` appears in result
  - **(4d)** injective forward provenance map (no duplication)
  - **(4e)** injective reverse completeness map — together with (4d), a bijection between
    result records and unexpired source records -/
@[step]
theorem gc_spec_64 (self : chain.KeyHistory) (current_key : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_bound : self.data.length ≤ Usize.max)
    (h_data_aligned : self.data.length % 36 = 0)
    (h_ooo : params.max_ooo_keys.val < 390451572)
    (h_key_ge : let max_ooo := if 0#u32 < params.max_ooo_keys then params.max_ooo_keys.val else 2000
                let trim_threshold := (max_ooo * 11 / 10 + 1) * 36
                trim_threshold ≤ self.data.length → max_ooo ≤ current_key.val)
    (h_platform : System.Platform.numBits = 64) :
    gc self current_key params ⦃ (result : chain.KeyHistory) =>
      GcPost self current_key params result ⦄ := by
  have h_usize : Usize.max = 2 ^ 64 - 1 := by
    simp [Usize.max, Usize.numBits, h_platform]
  exact gc_spec_core self current_key params h_bound h_data_aligned h_ooo (by omega) h_key_ge

end spqr.chain.KeyHistory
