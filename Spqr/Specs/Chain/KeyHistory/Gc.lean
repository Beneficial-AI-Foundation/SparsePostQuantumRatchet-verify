/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.KeyHistory.KEY_SIZE
import Spqr.Specs.Chain.ChainParams.TrimSize
import Spqr.Specs.Chain.ChainParams.MaxOooKeysOrDefault
import Spqr.Specs.Aeneas.IndexRangeFull
import Spqr.Specs.Chain.KeyHistory.Remove
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
      · simp only [bind_tc_ok]
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
    (h_data_aligned : self.data.length % 36 = 0)
    (h_i1_bound : i1.val ≤ self.data.length) :
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
  by_cases h_lt : i1.val < self.data.length
  · split
    · have h4 : i1.val + 4 ≤ self.data.length := by omega
      step*
      simp only [Slice.Insts.CoreCmpOrd.cmp_eq, alloc.vec.Vec.length, not_lt]
      rw [i3_post] at s_post1
      rw [s_post1]
      obtain ⟨o, ho⟩ :=
        lexCmpAux_OrdU8_ok trim_horizon.val (self.data.val.slice i1.val (i1.val + 4))
      rw [ho]
      cases o
      · simp only [bind_tc_ok, Bool.false_eq_true, if_false]
        rw [h_i]
        step*
        refine ⟨h_lt, fun h => absurd h (by simp), fun _ => ⟨i4_post, ?_, ?_⟩⟩
        · rw [i4_post]; omega
        · rw [i4_post]; grind
      · simp only [bind_tc_ok, Bool.false_eq_true, if_false]
        rw [h_i]
        step*
        refine ⟨h_lt, fun h => absurd h (by simp), fun _ => ⟨i4_post, ?_, ?_⟩⟩
        · rw [i4_post]; omega
        · rw [i4_post]; grind
      · simp only [bind_tc_ok, if_true]
        have h36 : i1 + 36#usize ≤ self.data.length := by scalar_tac
        have hspec := remove_spec self i1 params h36
        step*
        refine ⟨h_lt, self1_post1, h_aligned, by scalar_tac,
          by scalar_tac, ?_, self1_post3, self1_post4,
          fun h => absurd rfl h⟩
        intro j hj
        have := self1_post2 j hj
        grind
    · have h4 : i1.val + 4 ≤ self.data.length := by omega
      step*
  · step*


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

set_option maxHeartbeats 1600000 in
-- haevy grind
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
      result.length % 36 = 0 ∧
      result.length ≤ Usize.max ∧
      result.length ≤ self.data.length ∧
      (∀ j, j < i1.val → result.val[j]! = self.data.val[j]!) ∧
      i1.val ≤ result.length ∧
      (∀ m, i1.val ≤ m ∧  m < result.length ∧  m % 36 = 0 →
        Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val
          (result.val.slice m (m + 4)) ≠ ok .gt) ∧
      (∀ m, m < result.length ∧ m % 36 = 0 →
        ∃ n, n < self.data.length ∧ n % 36 = 0 ∧
          result.val.slice m (m + 36) = self.data.val.slice n (n + 36)) ∧
      (∀ n, n < self.data.length ∧ n % 36 = 0 →
        Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val
          (self.data.val.slice n (n + 4)) ≠ ok .gt →
        ∃ m, m < result.length ∧ m % 36 = 0 ∧
          result.val.slice m (m + 36) = self.data.val.slice n (n + 36)) ∧
      (∃ f : Nat → Nat,
        (∀ m, m < result.length ∧ m % 36 = 0 →
          f m < self.data.length ∧ (f m) % 36 = 0 ∧
          result.val.slice m (m + 36) =
            self.data.val.slice (f m) (f m + 36)) ∧
        (∀ m₁ m₂, m₁ < result.length ∧ m₁ % 36 = 0 →
          m₂ < result.length ∧ m₂ % 36 = 0 →
          f m₁ = f m₂ → m₁ = m₂)) ∧
      -- completeness with injectivity: injective reverse mapping from unexpired source to result
      (∃ g : Nat → Nat,
        (∀ n, n < self.data.length ∧ n % 36 = 0 →
          Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val
            (self.data.val.slice n (n + 4)) ≠ ok .gt →
          g n < result.length ∧ (g n) % 36 = 0 ∧
          result.val.slice (g n) (g n + 36) = self.data.val.slice n (n + 36)) ∧
        (∀ n₁ n₂, n₁ < self.data.length ∧ n₁ % 36 = 0 →
          n₂ < self.data.length ∧ n₂ % 36 = 0 →
          Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val
            (self.data.val.slice n₁ (n₁ + 4)) ≠ ok .gt →
          Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val
            (self.data.val.slice n₂ (n₂ + 4)) ≠ ok .gt →
          g n₁ = g n₂ → n₁ = n₂))⦄ := by
  unfold gc_loop
  apply loop.spec_decr_nat
    (measure := fun (p : chain.KeyHistory × Usize) => p.1.data.length - p.2.val)
    (inv := fun (p : chain.KeyHistory × Usize) =>
      p.2.val % 36 = 0 ∧ p.1.data.length % 36 = 0 ∧
      p.1.data.length ≤ Usize.max ∧ p.2.val ≤ p.1.data.length ∧
      p.1.data.length ≤ self.data.length ∧
      i1.val ≤ p.2.val ∧
      (∀ j, j < i1.val → p.1.data.val[j]! = self.data.val[j]!) ∧
      (∀ m, i1.val ≤ m ∧  m < p.2.val ∧  m % 36 = 0 →
        Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val
          (p.1.data.val.slice m (m + 4)) ≠ ok .gt) ∧
      (∀ m, m < p.1.data.length ∧ m % 36 = 0 →
        ∃ n, n < self.data.length ∧ n % 36 = 0 ∧
          p.1.data.val.slice m (m + 36) = self.data.val.slice n (n + 36)) ∧
      -- completeness: every unexpired record in the original self.data is retained
      (∀ n, n < self.data.length ∧ n % 36 = 0 →
        Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val
          (self.data.val.slice n (n + 4)) ≠ ok .gt →
        ∃ m, m < p.1.data.length ∧ m % 36 = 0 ∧
          p.1.data.val.slice m (m + 36) = self.data.val.slice n (n + 36)) ∧
      -- injective provenance: there exists an injective mapping from result records to source
      (∃ f : Nat → Nat,
        (∀ m, m < p.1.data.length ∧ m % 36 = 0 →
          f m < self.data.length ∧ (f m) % 36 = 0 ∧
          p.1.data.val.slice m (m + 36) =
            self.data.val.slice (f m) (f m + 36)) ∧
        (∀ m₁ m₂, m₁ < p.1.data.length ∧ m₁ % 36 = 0 →
          m₂ < p.1.data.length ∧ m₂ % 36 = 0 →
          f m₁ = f m₂ → m₁ = m₂)) ∧
      -- injective reverse mapping: from unexpired source records to current state records
      (∃ g : Nat → Nat,
        (∀ n, n < self.data.length ∧ n % 36 = 0 →
          Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val
            (self.data.val.slice n (n + 4)) ≠ ok .gt →
          g n < p.1.data.length ∧ (g n) % 36 = 0 ∧
          p.1.data.val.slice (g n) (g n + 36) = self.data.val.slice n (n + 36)) ∧
        (∀ n₁ n₂, n₁ < self.data.length ∧ n₁ % 36 = 0 →
          n₂ < self.data.length ∧ n₂ % 36 = 0 →
          Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val
            (self.data.val.slice n₁ (n₁ + 4)) ≠ ok .gt →
          Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val
            (self.data.val.slice n₂ (n₂ + 4)) ≠ ok .gt →
          g n₁ = g n₂ → n₁ = n₂)))
  · intro ⟨s, k⟩ ⟨hk_al, hs_al, hs_bnd, hkb, hs_le, hmono, hpres, hlive, hsubseq, hcomplete,
      ⟨f_inv, hf_prov, hf_inj⟩, ⟨g_inv, hg_prov, hg_inj⟩⟩
    have hspec := gc_loop.body_spec i params trim_horizon s k h_i hs_bnd hk_al hs_al hkb
    apply WP.spec_mono hspec
    intro cf hcf
    rcases cf with ⟨s', k'⟩ | out
    · obtain ⟨hlt, hrem, hadv⟩ := hcf
      by_cases hcmp : Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val
          (s.data.val.slice k.val (k.val + 4)) = ok .gt
      · obtain ⟨hlen, hkeq, hal, hib, hbnd', hpre, hsw, htr⟩ := hrem hcmp
        refine ⟨⟨hal, ?_, hbnd', hib, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · rw [hlen]
          grind
        · rw [hlen]
          grind
        · rw [hkeq]
          exact hmono
        · intro j hj
          have hjk : j < k.val := lt_of_lt_of_le hj hmono
          grind
        · intro m hm1 hm2
          rw [hkeq] at hm2
          have hm4 : m + 4 ≤ k.val := by grind
          have hibk : k.val ≤ s'.data.length := by rw [hkeq] at hib; exact hib
          have hsl : s'.data.val.slice m (m + 4) = s.data.val.slice m (m + 4) := by
            apply slice_eq_of_prefix
            · exact le_trans hm4 hibk
            · exact le_trans hm4 hkb
            · intro j hj
              exact hpre j (by omega)
          grind
        · intro m ⟨hml, hmal⟩
          have hml_s : m < s.data.length := by grind
          by_cases hmk : m + 36 ≤ k.val
          · obtain ⟨n, hn1, hn2, hn3⟩ := hsubseq m ⟨hml_s, hmal⟩
            have hml36 : m + 36 ≤ s'.data.length := by
              have : s'.data.length % 36 = 0 := by rw [hlen]; grind
              grind
            have hn36 : n + 36 ≤ self.data.length := by grind
            refine ⟨n, hn1, hn2,
              slice_eq_of_getElem! _ _ _ _ 36 hml36 hn36 fun j hj => ?_⟩
            change (s'.data)[m + j]! = (self.data)[n + j]!
            rw [hpre (m + j) (by omega)]
            exact getElem!_of_slice_eq _ _ _ _ 36 hn3 (by grind) hn36 j hj
          · by_cases hmk2 : k.val + 36 < s.data.length
            · have hsw' := hsw hmk2
              by_cases hmeq : m = k.val
              · subst hmeq
                have hlast_m : s.data.length - 36 < s.data.length := by omega
                have hlast_al : (s.data.length - 36) % 36 = 0 := by grind
                obtain ⟨n, hn1, hn2, hn3⟩ := hsubseq (s.data.length - 36) ⟨hlast_m, hlast_al⟩
                have hn36' : n + 36 ≤ self.data.length := by grind
                refine ⟨n, hn1, hn2,
                  slice_eq_of_getElem! _ _ _ _ 36 (by grind) hn36' fun j hj => ?_⟩
                rw [hsw', List.getElem!_take_of_lt _ _ _ (by omega),
                    List.getElem!_setSlice!_middle _ _ _ _
                      ⟨by omega, by simp [List.length_drop]; grind, by grind⟩,
                    List.getElem!_drop]
                have key := getElem!_of_slice_eq _ _ _ _ 36 hn3 (by grind) hn36' j hj
                have : s.data.val.length - 36 + j = s.data.val.length - 36 + (j + k.val - k.val) :=
                  by omega
                rw [this] at key
                grind
              · have hm_gt36 : k.val + 36 ≤ m := by grind
                obtain ⟨n, hn1, hn2, hn3⟩ := hsubseq m ⟨hml_s, hmal⟩
                have hn36' : n + 36 ≤ self.data.length := by grind
                refine ⟨n, hn1, hn2,
                  slice_eq_of_getElem! _ _ _ _ 36 (by grind) hn36' fun j hj => ?_⟩
                rw [hsw', List.getElem!_take_of_lt _ _ _ (by grind),
                    List.getElem!_setSlice!_suffix _ _ _ _ (by simp [List.length_drop]; omega)]
                exact getElem!_of_slice_eq _ _ _ _ 36 hn3 (by grind) hn36' j hj
            · have hk36 : k.val + 36 = s.data.length := by grind
              have htr' := htr hk36
              have hml' : m < k.val := by grind
              obtain ⟨n, hn1, hn2, hn3⟩ := hsubseq m ⟨hml_s, hmal⟩
              have hn36' : n + 36 ≤ self.data.length := by grind
              refine ⟨n, hn1, hn2,
                slice_eq_of_getElem! _ _ _ _ 36 (by grind) hn36' fun j hj => ?_⟩
              rw [htr', List.getElem!_take_of_lt _ _ _ (by grind)]
              exact getElem!_of_slice_eq _ _ _ _ 36 hn3 (by grind) hn36' j hj
        · intro n ⟨hn_lt, hn_al⟩ hn_live
          obtain ⟨m, hm_lt, hm_al, hm_eq⟩ := hcomplete n ⟨hn_lt, hn_al⟩ hn_live
          by_cases hmk_eq : m = k.val
          · subst hmk_eq
            have h4 : s.data.val.slice k.val (k.val + 4) =
                self.data.val.slice n (n + 4) := by
              apply slice_eq_of_getElem! _ _ _ _ 4 (by grind) (by grind)
              intro j hj
              exact getElem!_of_slice_eq _ _ _ _ 36 hm_eq (by grind) (by grind) j (by omega)
            rw [h4] at hcmp; exact absurd hcmp hn_live
          · by_cases hmk_last : m = s.data.length - 36
            · by_cases hmk2 : k.val + 36 < s.data.length
              · have hsw' := hsw hmk2
                refine ⟨k.val, by (rw [hlen]; omega), hk_al,
                  slice_eq_of_getElem! _ _ _ _ 36 (by grind) (by grind) fun j hj => ?_⟩
                rw [hsw', List.getElem!_take_of_lt _ _ _ (by grind),
                    List.getElem!_setSlice!_middle _ _ _ _
                      ⟨by omega, by simp [List.length_drop]; grind, by grind⟩,
                    List.getElem!_drop]
                have key := getElem!_of_slice_eq _ _ _ _ 36 hm_eq (by grind) (by grind) j hj
                convert key using 2
                omega
              · have : k.val + 36 = s.data.length := by grind
                omega
            · have hm_lt' : m < s'.data.length := by
                rw [hlen]
                have : m + 36 ≤ s.data.length := by
                  have := Nat.mod_add_div m 36
                  have := Nat.mod_add_div s.data.length 36
                  grind
                omega
              refine ⟨m, hm_lt', hm_al,
                slice_eq_of_getElem! _ _ _ _ 36 (by grind) (by grind) fun j hj => ?_⟩
              by_cases hmk2 : k.val + 36 < s.data.length
              · have hsw' := hsw hmk2
                rw [hsw', List.getElem!_take_of_lt _ _ _ (by grind)]
                by_cases hm_before_k : m + 36 ≤ k.val
                · rw [List.getElem!_setSlice!_prefix _ _ _ _ (by omega)]
                  exact getElem!_of_slice_eq _ _ _ _ 36 hm_eq (by grind) (by grind) j hj
                · have : k.val + 36 ≤ m := by grind
                  rw [List.getElem!_setSlice!_suffix _ _ _ _
                    (by simp [List.length_drop]; omega)]
                  exact getElem!_of_slice_eq _ _ _ _ 36 hm_eq (by grind) (by grind) j hj
              · have hk36 : k.val + 36 = s.data.length := by grind
                rw [htr hk36, List.getElem!_take_of_lt _ _ _ (by grind)]
                exact getElem!_of_slice_eq _ _ _ _ 36 hm_eq (by grind) (by grind) j hj
        · let f' : Nat → Nat := fun m =>
            if m = k.val ∧ k.val + 36 < s.data.length then f_inv (s.data.length - 36)
            else f_inv m
          refine ⟨f', fun m ⟨hml, hmal⟩ => ?_, fun m₁ m₂ ⟨hm1l, hm1a⟩ ⟨hm2l, hm2a⟩ hfeq => ?_⟩
          · change f' m < self.data.length ∧ (f' m) % 36 = 0 ∧
              s'.data.val.slice m (m + 36) = self.data.val.slice (f' m) (f' m + 36)
            simp only [f']
            by_cases hmeq_and_swap : m = k.val ∧ k.val + 36 < s.data.length
            · simp only [hmeq_and_swap]
              obtain ⟨hmeq, hswap⟩ := hmeq_and_swap
              subst hmeq
              have hlast_m : s.data.length - 36 < s.data.length := by omega
              have hlast_al : (s.data.length - 36) % 36 = 0 := by grind
              obtain ⟨hn1, hn2, hn3⟩ := hf_prov (s.data.length - 36) ⟨hlast_m, hlast_al⟩
              refine ⟨hn1, hn2, ?_⟩
              have hsw' := hsw hswap
              apply slice_eq_of_getElem! _ _ _ _ 36 (by grind) (by grind)
              intro j hj
              rw [hsw', List.getElem!_take_of_lt _ _ _ (by omega),
                  List.getElem!_setSlice!_middle _ _ _ _
                    ⟨by omega, by simp [List.length_drop]; grind, by grind⟩,
                  List.getElem!_drop]
              have key := getElem!_of_slice_eq _ _ _ _ 36 hn3 (by grind) (by grind) j hj
              have : s.data.val.length - 36 + j = s.data.val.length - 36 + (j + k.val - k.val) :=
                by omega
              rw [this] at key
              grind
            · simp only [hmeq_and_swap, if_false]
              have hml_s : m < s.data.length := by grind
              obtain ⟨hn1, hn2, hn3⟩ := hf_prov m ⟨hml_s, hmal⟩
              refine ⟨hn1, hn2, ?_⟩
              apply slice_eq_of_getElem! _ _ _ _ 36 (by grind) (by grind)
              intro j hj
              by_cases hmk2 : k.val + 36 < s.data.length
              · have hsw' := hsw hmk2
                have hm_ne_k : m ≠ k.val := by
                  intro heq; exact hmeq_and_swap ⟨heq, hmk2⟩
                by_cases hmk : m + 36 ≤ k.val
                · rw [hsw', List.getElem!_take_of_lt _ _ _ (by omega),
                      List.getElem!_setSlice!_prefix _ _ _ _ (by omega)]
                  exact getElem!_of_slice_eq _ _ _ _ 36 hn3 (by grind) (by grind) j hj
                · have hm_gt : k.val + 36 ≤ m := by grind
                  rw [hsw', List.getElem!_take_of_lt _ _ _ (by grind),
                      List.getElem!_setSlice!_suffix _ _ _ _ (by simp [List.length_drop]; omega)]
                  exact getElem!_of_slice_eq _ _ _ _ 36 hn3 (by grind) (by grind) j hj
              · have hk36 : k.val + 36 = s.data.length := by grind
                have hml' : m < k.val := by
                  have : ¬(m = k.val ∧ k.val + 36 < s.data.length) := hmeq_and_swap
                  grind
                rw [htr hk36, List.getElem!_take_of_lt _ _ _ (by grind)]
                exact getElem!_of_slice_eq _ _ _ _ 36 hn3 (by grind) (by grind) j hj
          · show m₁ = m₂
            simp only [f'] at hfeq
            by_cases h1 : m₁ = k.val ∧ k.val + 36 < s.data.length <;>
            by_cases h2 : m₂ = k.val ∧ k.val + 36 < s.data.length
            · exact h1.1.trans h2.1.symm
            · have hfeq' : f_inv (s.data.length - 36) = f_inv m₂ := by
                rw [if_pos h1, if_neg h2] at hfeq; exact hfeq
              have hm2_s : m₂ < s.data.length := by grind
              have hlast : s.data.length - 36 < s.data.length := by omega
              have hlast_al : (s.data.length - 36) % 36 = 0 := by grind
              have hm2_eq := hf_inj (s.data.length - 36) m₂ ⟨hlast, hlast_al⟩ ⟨hm2_s, hm2a⟩ hfeq'
              rw [hlen] at hm2l
              omega
            · have hfeq' : f_inv m₁ = f_inv (s.data.length - 36) := by
                rw [if_neg h1, if_pos h2] at hfeq; exact hfeq
              have hm1_s : m₁ < s.data.length := by grind
              have hlast : s.data.length - 36 < s.data.length := by omega
              have hlast_al : (s.data.length - 36) % 36 = 0 := by grind
              have hm1_eq := hf_inj m₁ (s.data.length - 36) ⟨hm1_s, hm1a⟩ ⟨hlast, hlast_al⟩ hfeq'
              rw [hlen] at hm1l
              omega
            · have hfeq' : f_inv m₁ = f_inv m₂ := by
                rw [if_neg h1, if_neg h2] at hfeq; exact hfeq
              have hm1_s : m₁ < s.data.length := by grind
              have hm2_s : m₂ < s.data.length := by grind
              exact hf_inj m₁ m₂ ⟨hm1_s, hm1a⟩ ⟨hm2_s, hm2a⟩ hfeq'
        · let g' : Nat → Nat := fun n =>
            if g_inv n = s.data.length - 36 ∧ k.val + 36 < s.data.length then k.val
            else g_inv n
          refine ⟨g', fun n ⟨hn_lt, hn_al⟩ hn_live => ?_,
            fun n₁ n₂ ⟨hn1_lt, hn1_al⟩ ⟨hn2_lt, hn2_al⟩ hn1_live hn2_live hgeq => ?_⟩
          · obtain ⟨hgn_lt, hgn_al, hgn_eq⟩ := hg_prov n ⟨hn_lt, hn_al⟩ hn_live
            simp only [g']
            by_cases hg_last_swap : g_inv n = s.data.length - 36 ∧ k.val + 36 < s.data.length
            · obtain ⟨hg_last, hswap⟩ := hg_last_swap
              simp only [show g_inv n = s.data.length - 36 from hg_last,
                show k.val + 36 < s.data.length from hswap, and_self, ite_true]
              refine ⟨by (rw [hlen]; omega), hk_al, ?_⟩
              have hsw' := hsw hswap
              apply slice_eq_of_getElem! _ _ _ _ 36 (by grind) (by grind)
              intro j hj
              rw [hsw', List.getElem!_take_of_lt _ _ _ (by grind),
                  List.getElem!_setSlice!_middle _ _ _ _
                    ⟨by omega, by simp [List.length_drop]; grind, by grind⟩,
                  List.getElem!_drop]
              have key := getElem!_of_slice_eq _ _ _ _ 36 hgn_eq (by grind) (by grind) j hj
              rw [hg_last] at key; convert key using 2; omega
            · simp only [hg_last_swap, if_false]
              have hgn_ne_k : g_inv n ≠ k.val := by
                intro heq
                have h4_eq : s.data.val.slice k.val (k.val + 4) =
                    self.data.val.slice n (n + 4) := by
                  rw [← heq]
                  apply slice_eq_of_getElem! _ _ _ _ 4 (by grind) (by grind)
                  intro j hj
                  exact getElem!_of_slice_eq _ _ _ _ 36 hgn_eq (by grind) (by grind) j (by omega)
                rw [h4_eq] at hcmp; exact absurd hcmp hn_live
              have hgn_lt' : g_inv n < s'.data.length := by
                rw [hlen]
                have : g_inv n + 36 ≤ s.data.length := by grind
                by_cases heq_last : g_inv n = s.data.length - 36
                · have : ¬(k.val + 36 < s.data.length) := fun h => hg_last_swap ⟨heq_last, h⟩
                  have : k.val + 36 = s.data.length := by grind
                  omega
                · omega
              refine ⟨hgn_lt', hgn_al, ?_⟩
              apply slice_eq_of_getElem! _ _ _ _ 36 (by grind) (by grind)
              intro j hj
              by_cases hmk2 : k.val + 36 < s.data.length
              · have hsw' := hsw hmk2
                rw [hsw', List.getElem!_take_of_lt _ _ _ (by grind)]
                by_cases hgn_before_k : g_inv n + 36 ≤ k.val
                · rw [List.getElem!_setSlice!_prefix _ _ _ _ (by omega)]
                  exact getElem!_of_slice_eq _ _ _ _ 36 hgn_eq (by grind) (by grind) j hj
                · have : k.val + 36 ≤ g_inv n := by grind
                  rw [List.getElem!_setSlice!_suffix _ _ _ _ (by simp [List.length_drop]; omega)]
                  exact getElem!_of_slice_eq _ _ _ _ 36 hgn_eq (by grind) (by grind) j hj
              · have hk36 : k.val + 36 = s.data.length := by grind
                rw [htr hk36, List.getElem!_take_of_lt _ _ _ (by grind)]
                exact getElem!_of_slice_eq _ _ _ _ 36 hgn_eq (by grind) (by grind) j hj
          · show n₁ = n₂
            simp only [g'] at hgeq
            by_cases h1 : g_inv n₁ = s.data.length - 36 ∧ k.val + 36 < s.data.length <;>
            by_cases h2 : g_inv n₂ = s.data.length - 36 ∧ k.val + 36 < s.data.length
            · exact hg_inj n₁ n₂ ⟨hn1_lt, hn1_al⟩ ⟨hn2_lt, hn2_al⟩ hn1_live hn2_live
                (by rw [h1.1, h2.1])
            · rw [if_pos h1, if_neg h2] at hgeq
              have hgn2_eq_k : g_inv n₂ = k.val := hgeq.symm
              obtain ⟨_, _, hgn2_sl⟩ := hg_prov n₂ ⟨hn2_lt, hn2_al⟩ hn2_live
              have h4_eq : s.data.val.slice k.val (k.val + 4) =
                  self.data.val.slice n₂ (n₂ + 4) := by
                rw [← hgn2_eq_k]
                apply slice_eq_of_getElem! _ _ _ _ 4 (by grind) (by grind)
                intro j hj
                exact getElem!_of_slice_eq _ _ _ _ 36 hgn2_sl (by grind) (by grind) j (by omega)
              rw [h4_eq] at hcmp; exact absurd hcmp hn2_live
            · rw [if_neg h1, if_pos h2] at hgeq
              have hgn1_eq_k : g_inv n₁ = k.val := hgeq
              obtain ⟨_, _, hgn1_sl⟩ := hg_prov n₁ ⟨hn1_lt, hn1_al⟩ hn1_live
              have h4_eq : s.data.val.slice k.val (k.val + 4) =
                  self.data.val.slice n₁ (n₁ + 4) := by
                rw [← hgn1_eq_k]
                apply slice_eq_of_getElem! _ _ _ _ 4 (by grind) (by grind)
                intro j hj
                exact getElem!_of_slice_eq _ _ _ _ 36 hgn1_sl (by grind) (by grind) j (by omega)
              rw [h4_eq] at hcmp; exact absurd hcmp hn1_live
            · rw [if_neg h1, if_neg h2] at hgeq
              exact hg_inj n₁ n₂ ⟨hn1_lt, hn1_al⟩ ⟨hn2_lt, hn2_al⟩ hn1_live hn2_live hgeq
        · simp only; rw [hlen] at hib ⊢; grind
      · obtain ⟨hself, hkeq, hal, hib, _hbnd, _hal2⟩ := hadv hcmp
        subst hself
        refine ⟨⟨hal, hs_al, hs_bnd, hib, hs_le, ?_, hpres, ?_, hsubseq, hcomplete,
          ⟨f_inv, hf_prov, hf_inj⟩, ⟨g_inv, hg_prov, hg_inj⟩⟩, ?_⟩
        · grind
        · intro m hm1 hm2
          by_cases hmk : m < k.val
          · grind
          · have hmeq : m = k.val := by grind
            grind
        · simp only; omega
    · obtain ⟨hout, _hnlt⟩ := hcf
      subst hout
      refine ⟨hs_al, hs_bnd, hs_le, hpres, le_trans hmono hkb, ?_, ?_, ?_, ?_, ?_⟩
      · intro m ⟨hm1, hm2, hm3⟩
        have : m < k.val := by omega
        exact hlive m ⟨hm1, this, hm3⟩
      · intro m hm; exact hsubseq m hm
      · intro n hn hn_live; exact hcomplete n hn hn_live
      · exact ⟨f_inv, hf_prov, hf_inj⟩
      · exact ⟨g_inv, hg_prov, hg_inj⟩
  · exact ⟨h_aligned, h_data_aligned, h_bound, h_i1_bound, le_refl _, le_refl _,
      fun j _ => rfl, fun m h => by grind,
      fun m ⟨hml, hmal⟩ => ⟨m, hml, hmal, rfl⟩,
      fun n ⟨hn_lt, hn_al⟩ _ => ⟨n, hn_lt, hn_al, rfl⟩,
      ⟨fun m => m, fun m ⟨hml, hmal⟩ => ⟨hml, hmal, rfl⟩,
       fun _ _ _ _ h => h⟩,
      ⟨fun n => n, fun n ⟨hn_lt, hn_al⟩ _ => ⟨hn_lt, hn_al, rfl⟩,
       fun _ _ _ _ _ _ h => h⟩⟩


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
      let max_ooo : Nat :=
        if 0#u32 < params.max_ooo_keys then params.max_ooo_keys.val else 2000
      let trim_size : Nat := max_ooo * 11 / 10 + 1
      let trim_threshold : Nat := trim_size * 36
      -- (1) alignment: result length is a multiple of 36 (whole records)
      result.data.length % 36 = 0 ∧
      -- (2) shrinkage: GC only removes records, never grows
      result.data.length ≤ self.data.length ∧
      -- (3) no-op when below threshold: if data is small enough, nothing is removed
      (self.data.length < trim_threshold → result = self) ∧
      -- (4) when above threshold, GC computes a trim horizon and enforces:
      (trim_threshold ≤ self.data.length →
        ∃ horizon : U32,
         -- (4a) horizon value: `current_key - max_ooo`
         horizon.val = current_key.val - max_ooo ∧
          -- (4b) liveness: every record in result is unexpired (counter ≥ horizon)
          (∀ m, m < result.data.length ∧ m % 36 = 0 →
            Slice.lexCmpAux core.cmp.OrdU8
              (horizon.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8))
              (result.data.val.slice m (m + 4)) ≠ ok .gt) ∧
          -- (4c) completeness: every unexpired record in self.data is retained in result
          (∀ n, n < self.data.length ∧ n % 36 = 0 →
            Slice.lexCmpAux core.cmp.OrdU8
              (horizon.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8))
              (self.data.val.slice n (n + 4)) ≠ ok .gt →
            ∃ m, m < result.data.length ∧ m % 36 = 0 ∧
              result.data.val.slice m (m + 36) = self.data.val.slice n (n + 36)) ∧
          -- (4d) provenance with injectivity: there exists an injective mapping
          --      witnessing that every result record originated from a distinct
          --      source record (no duplication). Together with (4b) and (4c), this
          --      ensures multiset(result records) = multiset(live source records).
          (∃ f : Nat → Nat,
            (∀ m, m < result.data.length ∧ m % 36 = 0 →
              f m < self.data.length ∧ (f m) % 36 = 0 ∧
              result.data.val.slice m (m + 36) =
                self.data.val.slice (f m) (f m + 36)) ∧
            (∀ m₁ m₂, m₁ < result.data.length ∧ m₁ % 36 = 0 →
              m₂ < result.data.length ∧ m₂ % 36 = 0 →
              f m₁ = f m₂ → m₁ = m₂)) ∧
          -- (4e) completeness with injectivity: injective reverse mapping from
          --      unexpired source records to result records. Together with (4d),
          --      establishes a bijection proving
          --      multiset(result records) = multiset(unexpired source records).
          (∃ g : Nat → Nat,
            (∀ n, n < self.data.length ∧ n % 36 = 0 →
              Slice.lexCmpAux core.cmp.OrdU8
                (horizon.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8))
                (self.data.val.slice n (n + 4)) ≠ ok .gt →
              g n < result.data.length ∧ (g n) % 36 = 0 ∧
              result.data.val.slice (g n) (g n + 36) =
                self.data.val.slice n (n + 36)) ∧
            (∀ n₁ n₂, n₁ < self.data.length ∧ n₁ % 36 = 0 →
              n₂ < self.data.length ∧ n₂ % 36 = 0 →
              Slice.lexCmpAux core.cmp.OrdU8
                (horizon.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8))
                (self.data.val.slice n₁ (n₁ + 4)) ≠ ok .gt →
              Slice.lexCmpAux core.cmp.OrdU8
                (horizon.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8))
                (self.data.val.slice n₂ (n₂ + 4)) ≠ ok .gt →
              g n₁ = g n₂ → n₁ = n₂))) ⦄ := by
  unfold gc
  simp only [alloc.vec.Vec.len]
  step*
  · simp only [DEFAULT_CHAIN_PARAMS_spec] at *
    rw [i2_post] at i3_post
    simp only [UScalar.ofNatCore_val_eq] at i3_post
    by_cases hpos : params.max_ooo_keys > 0#u32
    · have hi4 : i4 = params.max_ooo_keys := i4_post1.mpr hpos
      have hi1 : i1.val = params.max_ooo_keys.val * 11 / 10 + 1 := i1_post1.mpr hpos
      rw [hi1] at i3_post
      rw [hi4]
      have hlt : 0#u32 < params.max_ooo_keys := by scalar_tac
      rw [if_pos hlt] at h_key_ge
      grind
    · have hzero : ¬(params.max_ooo_keys > 0#u32) := hpos
      have hi4 : i4.val = 2000 := by
        have := i4_post2.mpr (Or.inl (by scalar_tac))
        scalar_tac
      have hi1_val : i1.val = 2201 := by
        have := i1_post2.mpr (Or.inl (by scalar_tac))
        scalar_tac
      rw [hi1_val] at i3_post
      have hlt : ¬(0#u32 < params.max_ooo_keys) := by scalar_tac
      rw [if_neg hlt] at h_key_ge
      scalar_tac
  · simp only [DEFAULT_CHAIN_PARAMS_spec] at *
    rw [i2_post] at i3_post
    simp only [UScalar.ofNatCore_val_eq] at i3_post
    refine ⟨v_post1, v_post3, fun h_lt => ?_, fun h_ge => ?_⟩
    · by_cases hpos : params.max_ooo_keys > 0#u32
      · have hi1 : i1.val = params.max_ooo_keys.val * 11 / 10 + 1 := i1_post1.mpr hpos
        rw [hi1] at i3_post
        have hlt' : 0#u32 < params.max_ooo_keys := by scalar_tac
        rw [if_pos hlt'] at h_lt
        grind
      · have hi1_val : i1.val = 2201 := by
          have := i1_post2.mpr (Or.inl (by scalar_tac))
          scalar_tac
        rw [hi1_val] at i3_post
        have hlt' : ¬(0#u32 < params.max_ooo_keys) := by scalar_tac
        rw [if_neg hlt'] at h_lt
        scalar_tac
    · refine ⟨i5, ?_, ?_, ?_, ?_, ?_⟩
      · by_cases hpos : params.max_ooo_keys > 0#u32
        · have hi4 : i4 = params.max_ooo_keys := i4_post1.mpr hpos
          rw [hi4] at i5_post1
          have hlt : 0#u32 < params.max_ooo_keys := by scalar_tac
          rw [if_pos hlt]
          omega
        · have hi4 : i4.val = 2000 := by
            have := i4_post2.mpr (Or.inl (by scalar_tac))
            scalar_tac
          have hlt : ¬(0#u32 < params.max_ooo_keys) := by scalar_tac
          rw [if_neg hlt]
          omega
      · intro m hml
        have := v_post6 m (by omega) hml
        simp only [Array.val_to_slice, a_post, UScalarTy.U8_numBits_eq, ne_eq] at this
        exact this
      · intro n  hn_live
        simp only [Array.to_slice, a_post, ne_eq, alloc.vec.Vec.length] at v_post8
        exact v_post8 n  hn_live
      · simp only [alloc.vec.Vec.length] at v_post9 v_post10
        exact ⟨_, v_post9, v_post10⟩
      · simp only [Array.to_slice, a_post] at v_post11 v_post12
        exact ⟨_, v_post11, v_post12⟩

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
      let max_ooo : Nat :=
        if 0#u32 < params.max_ooo_keys then params.max_ooo_keys.val else 2000
      let trim_size : Nat := max_ooo * 11 / 10 + 1
      let trim_threshold : Nat := trim_size * 36
      -- (1) alignment: result length is a multiple of 36 (whole records)
      result.data.length % 36 = 0 ∧
      -- (2) shrinkage: GC only removes records, never grows
      result.data.length ≤ self.data.length ∧
      -- (3) no-op when below threshold: if data is small enough, nothing is removed
      (self.data.length < trim_threshold → result = self) ∧
      -- (4) when above threshold, GC computes a trim horizon and enforces:
      (trim_threshold ≤ self.data.length →
        ∃ horizon : U32,
         -- (4a) horizon value: `current_key - max_ooo`
         horizon.val = current_key.val - max_ooo ∧
          -- (4b) liveness: every record in result is unexpired (counter ≥ horizon)
          (∀ m, m < result.data.length ∧ m % 36 = 0 →
            Slice.lexCmpAux core.cmp.OrdU8
              (horizon.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8))
              (result.data.val.slice m (m + 4)) ≠ ok .gt) ∧
          -- (4c) completeness: every unexpired record in self.data is retained in result
          (∀ n, n < self.data.length ∧ n % 36 = 0 →
            Slice.lexCmpAux core.cmp.OrdU8
              (horizon.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8))
              (self.data.val.slice n (n + 4)) ≠ ok .gt →
            ∃ m, m < result.data.length ∧ m % 36 = 0 ∧
              result.data.val.slice m (m + 36) = self.data.val.slice n (n + 36)) ∧
          -- (4d) provenance with injectivity: there exists an injective mapping
          --      witnessing that every result record originated from a distinct
          --      source record (no duplication). Together with (4b) and (4c), this
          --      ensures multiset(result records) = multiset(live source records).
          (∃ f : Nat → Nat,
            (∀ m, m < result.data.length ∧ m % 36 = 0 →
              f m < self.data.length ∧ (f m) % 36 = 0 ∧
              result.data.val.slice m (m + 36) =
                self.data.val.slice (f m) (f m + 36)) ∧
            (∀ m₁ m₂, m₁ < result.data.length ∧ m₁ % 36 = 0 →
              m₂ < result.data.length ∧ m₂ % 36 = 0 →
              f m₁ = f m₂ → m₁ = m₂)) ∧
          -- (4e) completeness with injectivity: injective reverse mapping from
          --      unexpired source records to result records. Together with (4d),
          --      establishes a bijection proving
          --      multiset(result records) = multiset(unexpired source records).
          (∃ g : Nat → Nat,
            (∀ n, n < self.data.length ∧ n % 36 = 0 →
              Slice.lexCmpAux core.cmp.OrdU8
                (horizon.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8))
                (self.data.val.slice n (n + 4)) ≠ ok .gt →
              g n < result.data.length ∧ (g n) % 36 = 0 ∧
              result.data.val.slice (g n) (g n + 36) =
                self.data.val.slice n (n + 36)) ∧
            (∀ n₁ n₂, n₁ < self.data.length ∧ n₁ % 36 = 0 →
              n₂ < self.data.length ∧ n₂ % 36 = 0 →
              Slice.lexCmpAux core.cmp.OrdU8
                (horizon.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8))
                (self.data.val.slice n₁ (n₁ + 4)) ≠ ok .gt →
              Slice.lexCmpAux core.cmp.OrdU8
                (horizon.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8))
                (self.data.val.slice n₂ (n₂ + 4)) ≠ ok .gt →
              g n₁ = g n₂ → n₁ = n₂))) ⦄ := by
  have h_usize : Usize.max = 2 ^ 64 - 1 := by
    simp [Usize.max, Usize.numBits, h_platform]
  unfold gc
  simp only [alloc.vec.Vec.len]
  step*
  · simp only [DEFAULT_CHAIN_PARAMS_spec] at *
    rw [i2_post] at i3_post
    simp only [UScalar.ofNatCore_val_eq] at i3_post
    by_cases hpos : params.max_ooo_keys > 0#u32
    · have hi4 : i4 = params.max_ooo_keys := i4_post1.mpr hpos
      have hi1 : i1.val = params.max_ooo_keys.val * 11 / 10 + 1 := i1_post1.mpr hpos
      rw [hi1] at i3_post
      rw [hi4]
      have hlt : 0#u32 < params.max_ooo_keys := by scalar_tac
      rw [if_pos hlt] at h_key_ge
      grind
    · have hzero : ¬(params.max_ooo_keys > 0#u32) := hpos
      have hi4 : i4.val = 2000 := by
        have := i4_post2.mpr (Or.inl (by scalar_tac))
        scalar_tac
      have hi1_val : i1.val = 2201 := by
        have := i1_post2.mpr (Or.inl (by scalar_tac))
        scalar_tac
      rw [hi1_val] at i3_post
      have hlt : ¬(0#u32 < params.max_ooo_keys) := by scalar_tac
      rw [if_neg hlt] at h_key_ge
      scalar_tac
  · simp only [DEFAULT_CHAIN_PARAMS_spec] at *
    rw [i2_post] at i3_post
    simp only [UScalar.ofNatCore_val_eq] at i3_post
    refine ⟨v_post1, v_post3, fun h_lt => ?_, fun h_ge => ?_⟩
    · by_cases hpos : params.max_ooo_keys > 0#u32
      · have hi1 : i1.val = params.max_ooo_keys.val * 11 / 10 + 1 := i1_post1.mpr hpos
        rw [hi1] at i3_post
        have hlt' : 0#u32 < params.max_ooo_keys := by scalar_tac
        rw [if_pos hlt'] at h_lt
        grind
      · have hi1_val : i1.val = 2201 := by
          have := i1_post2.mpr (Or.inl (by scalar_tac))
          scalar_tac
        rw [hi1_val] at i3_post
        have hlt' : ¬(0#u32 < params.max_ooo_keys) := by scalar_tac
        rw [if_neg hlt'] at h_lt
        scalar_tac
    · refine ⟨i5, ?_, ?_, ?_, ?_, ?_⟩
      · by_cases hpos : params.max_ooo_keys > 0#u32
        · have hi4 : i4 = params.max_ooo_keys := i4_post1.mpr hpos
          rw [hi4] at i5_post1
          have hlt : 0#u32 < params.max_ooo_keys := by scalar_tac
          rw [if_pos hlt]
          omega
        · have hi4 : i4.val = 2000 := by
            have := i4_post2.mpr (Or.inl (by scalar_tac))
            scalar_tac
          have hlt : ¬(0#u32 < params.max_ooo_keys) := by scalar_tac
          rw [if_neg hlt]
          omega
      · intro m hml
        have := v_post6 m (by omega) hml
        simp only [Array.val_to_slice, a_post, UScalarTy.U8_numBits_eq, ne_eq] at this
        exact this
      · intro n  hn_live
        simp only [Array.to_slice, a_post, ne_eq, alloc.vec.Vec.length] at v_post8
        exact v_post8 n  hn_live
      · simp only [alloc.vec.Vec.length] at v_post9 v_post10
        exact ⟨_, v_post9, v_post10⟩
      · simp only [Array.to_slice, a_post] at v_post11 v_post12
        exact ⟨_, v_post11, v_post12⟩

end spqr.chain.KeyHistory
