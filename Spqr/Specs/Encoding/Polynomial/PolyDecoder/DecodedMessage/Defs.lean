/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Math.Poly.Lagrange.InterpolantSum
public import Spqr.Math.Poly.Eval
import Spqr.Specs.Encoding.Polynomial.Pt.Cmp
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.PointsValid
import Spqr.Auxiliary.Aeneas.SpecImpExists

/-!
# Functional model of `PolyDecoder::decoded_message`

This file defines the pure mathematical model of the value reconstructed by
`decoded_message` for each index `k ∈ [0, pts_needed)`, mirroring the Rust code:

```rust
let poly = i % 16;
let poly_idx = i / 16;
let pt = Pt { x: GF16::new(poly_idx as u16), y: GF16::ZERO };
let y = if let Ok(i) = self.pts[poly].binary_search(&pt) {
    self.pts[poly][i].y
} else {
    polys[poly] = Some(Poly::lagrange_interpolate(points_vecs[poly]));  // lazily
    polys[poly].compute_at(pt.x)
};
out.push((y.value >> 8) as u8);
out.push(y.value as u8);
```

## Main definitions

* `lookupY` — model of `binary_search` on a list of `Pt` (whose `Ord` instance compares
  `x` only): the `y` of the first point whose `x` equals the target, or `none`.  Rust's
  `binary_search` may return *any* matching index; on a `SlotSorted` list (the `SortedSet<Pt>`
  invariant, see `PointsValid.lean`) the match is unique, so `lookupY` is faithful.  The
  generic spec is `binary_search_Pt_spec_generic`; `binary_search_Pt_spec` derives the
  `lookupY` form under `SlotSorted`.
* `necessaryPoints` — `pts_needed / 16 + (if poly < pts_needed % 16 then 1 else 0)`.
* `decodedValue` — the GF(2¹⁶) value decoded at index `k`.
* `BytesDecode` — the byte pairs `(bs[2k], bs[2k+1])` encode `decodedValue … (lo + k)`.

**Source**: spqr/src/encoding/polynomial.rs, lines 944:8-969:9
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder

/-- Model of `[Pt]::binary_search(&Pt { x, _ })`: scan the list, skipping points with a
smaller `x`; return the `y` of the first point with the same `x`, or `none` once a point
with a larger `x` is met or the list is exhausted.  On a sorted list this is exactly
Rust's `binary_search` (which only compares `x` coordinates for `Pt`). -/
def lookupY : List Pt → Nat → Option GF16
  | [], _ => none
  | p :: rest, x =>
    if p.x.value.val < x then lookupY rest x
    else if p.x.value.val = x then some p.y
    else none

/-- `PolyDecoder::necessary_points(poly)` as a pure function. -/
def necessaryPoints (pts_needed : Usize) (poly : Nat) : Nat :=
  pts_needed.val / 16 + (if poly < pts_needed.val % 16 then 1 else 0)

/-- The GF(2¹⁶) value reconstructed by `decoded_message` at index `k`:
  * `poly := k % 16`, `x := (k / 16) as u16`;
  * if slot `poly` stores a point with abscissa `x`, its ordinate;
  * otherwise the Lagrange interpolant through the first `necessaryPoints pts_needed poly`
    points of slot `poly`, evaluated at `x`. -/
noncomputable def decodedValue
    (a : Array (sorted_vec.SortedSet Pt) 16#usize) (pts_needed : Usize) (k : Nat) : GF216 :=
  let poly := k % 16
  let x := (k / 16) % 2 ^ 16
  let l : List Pt := (a.val[poly]'(by simp; omega)).val
  match lookupY l x with
  | some y => y.toGF216
  | none =>
    let np := necessaryPoints pts_needed poly
    (lagrangeInterpolantSum (l.take np) np).eval x.toGF216

/-- The cached polynomial for slot `j` (if any) is the Lagrange interpolant through the
first `necessaryPoints pts_needed j` points of slot `j`. -/
def CacheOk (a : Array (sorted_vec.SortedSet Pt) 16#usize) (pts_needed : Usize)
    (polys : Array (Option Poly) 16#usize) : Prop :=
  ∀ j (hj : j < 16) (p : Poly), polys.val[j]'(by simp; omega) = some p →
    p.toGF216Poly =
      lagrangeInterpolantSum ((a.val[j]'(by simp; omega)).val.take (necessaryPoints pts_needed j))
        (necessaryPoints pts_needed j)

/-- The byte list `bs` encodes the decoded values starting at index `lo`:
the big-endian pair `(bs[2k], bs[2k+1])` is `decodedValue a pts_needed (lo + k)`. -/
def BytesDecode (a : Array (sorted_vec.SortedSet Pt) 16#usize) (pts_needed : Usize)
    (bs : List U8) (lo : Nat) : Prop :=
  ∀ (k : Nat) (hi lo' : U8), bs[2 * k]? = some hi → bs[2 * k + 1]? = some lo' →
    (hi.val * 256 + lo'.val).toGF216 = decodedValue a pts_needed (lo + k)

theorem BytesDecode_nil (a : Array (sorted_vec.SortedSet Pt) 16#usize) (pts_needed : Usize)
    (lo : Nat) : BytesDecode a pts_needed [] lo := by
  intro k hi lo' h; simp at h

/-- Extending a decoding byte list by the byte pair of the next index. -/
theorem BytesDecode_append (a : Array (sorted_vec.SortedSet Pt) 16#usize) (pts_needed : Usize)
    (bs : List U8) (lo n : Nat) (hi lo' : U8)
    (h_len : bs.length = 2 * n)
    (h_bs : BytesDecode a pts_needed bs lo)
    (h_pair : (hi.val * 256 + lo'.val).toGF216 = decodedValue a pts_needed (lo + n)) :
    BytesDecode a pts_needed (bs ++ [hi, lo']) lo := by
  intro k h1 h2 hh1 hh2
  by_cases hk : k < n
  · rw [List.getElem?_append_left (by omega)] at hh1
    rw [List.getElem?_append_left (by omega)] at hh2
    exact h_bs k h1 h2 hh1 hh2
  · have hk' : k = n := by
      by_contra hne
      have : 2 * k + 1 ≥ bs.length + 2 := by omega
      rw [List.getElem?_eq_none (by simp; omega)] at hh2
      cases hh2
    subst hk'
    rw [List.getElem?_append_right (by omega)] at hh1
    rw [List.getElem?_append_right (by omega)] at hh2
    have e1 : 2 * k - bs.length = 0 := by omega
    have e2 : 2 * k + 1 - bs.length = 1 := by omega
    rw [e1] at hh1; rw [e2] at hh2
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hh1 hh2
    subst hh1 hh2
    exact h_pair

/-! ## `binary_search` on `Pt` lists

Rust's `binary_search` only promises that, on a match, *some* index of an element comparing
equal to the target is returned — which one is unspecified when several elements compare
equal.  The generic model `binarySearchAux_Pt_generic` therefore only says:

  • `Ok j` → `s[j].x = x` (any matching index);
  • `Err _` → (on a `SlotSorted` list) no element has abscissa `x`.

Under `SlotSorted` (strictly increasing abscissae, the `SortedSet<Pt>` invariant) the match is
unique, so `lookupY` — which scans for the first match — is a faithful characterisation.  This
is `binary_search_Pt_spec`, which requires `SlotSorted s.val`. -/

/-- Generic characterisation of `Slice.binarySearchAux` with the `Pt` ordering: `Ok j`
means the point at position `j - i` has abscissa `x`; `Err _` means (on a sorted list) no
point has abscissa `x`.  Which matching index is returned is left unspecified. -/
theorem binarySearchAux_Pt_generic (l : List Pt) (g : GF16) (i : Nat) :
    Slice.binarySearchAux Pt.Insts.CoreCmpOrd l { x := g, y := GF16.ZERO } i
      ⦃ (r : core.result.Result Nat Nat) =>
      match r with
      | .Ok j => i ≤ j ∧ ∃ (h : j - i < l.length),
          (l[j - i]'h).x.value.val = g.value.val
      | .Err j => j ≤ i + l.length ∧
          (PolyDecoder.SlotSorted l → ∀ p ∈ l, p.x.value.val ≠ g.value.val) ⦄ := by
  induction l generalizing i with
  | nil => simp [Slice.binarySearchAux]
  | cons p rest ih =>
    simp only [Slice.binarySearchAux, Pt.Insts.CoreCmpOrd.cmp_eq_compare, bind_ok]
    rcases Nat.lt_trichotomy p.x.value.val g.value.val with hlt | heq | hgt
    · rw [Nat.compare_eq_lt.mpr hlt]
      apply WP.spec_mono (ih (i + 1))
      intro r hr
      cases r with
      | Ok j =>
        obtain ⟨hij, hjl, hl⟩ := hr
        refine ⟨by omega, ?_⟩
        simp only [List.length_cons]
        refine ⟨by omega, ?_⟩
        have : j - i = (j - (i + 1)) + 1 := by omega
        simp only [this, List.getElem_cons_succ]
        exact hl
      | Err j =>
        obtain ⟨hjl, hl⟩ := hr
        refine ⟨by simp; omega, fun hs q hq => ?_⟩
        rw [PolyDecoder.SlotSorted, List.pairwise_cons] at hs
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact Nat.ne_of_lt hlt
        · exact hl hs.2 q hq
    · rw [Nat.compare_eq_eq.mpr heq]
      simp only [WP.spec_ok]
      exact ⟨le_refl _, by simp, by simpa using heq⟩
    · rw [Nat.compare_eq_gt.mpr hgt]
      simp only [WP.spec_ok]
      refine ⟨by simp, fun hs q hq => ?_⟩
      rw [PolyDecoder.SlotSorted, List.pairwise_cons] at hs
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact Nat.ne_of_gt hgt
      · exact Nat.ne_of_gt (lt_trans hgt (hs.1 q hq))

/-- `lookupY` on a `SlotSorted` list returns the ordinate of *the* (unique) point with
abscissa `x`, if any: for every index `j` with `l[j].x = x`, `lookupY l x = some l[j].y`. -/
theorem lookupY_eq_of_sorted (l : List Pt) (x : Nat) (hs : PolyDecoder.SlotSorted l)
    (j : Nat) (hj : j < l.length) (hx : (l[j]'hj).x.value.val = x) :
    lookupY l x = some (l[j]'hj).y := by
  induction l generalizing j with
  | nil => simp at hj
  | cons p rest ih =>
    rw [PolyDecoder.SlotSorted, List.pairwise_cons] at hs
    obtain ⟨hp, hrest⟩ := hs
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero] at hx ⊢
      simp [lookupY, hx]
    | succ j =>
      simp only [List.getElem_cons_succ] at hx ⊢
      have hlt : p.x.value.val < x := by
        rw [← hx]; exact hp _ (List.getElem_mem _)
      simp only [lookupY, hlt, ite_true]
      exact ih hrest j (by simpa using hj) hx

/-- `lookupY l x = none` when no point of `l` has abscissa `x`. -/
theorem lookupY_eq_none_of_forall (l : List Pt) (x : Nat)
    (h : ∀ p ∈ l, p.x.value.val ≠ x) : lookupY l x = none := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    have hne := h p (by simp)
    simp only [lookupY, hne, ite_false]
    split
    · exact ih fun q hq => h q (by simp [hq])
    · rfl


/-- `UScalar.tryMk .Usize n` succeeds with value `n` whenever `n ≤ Usize.max`. -/
theorem usize_tryMk_spec (n : Nat) (h : n ≤ Usize.max) :
    UScalar.tryMk .Usize n ⦃ (r : Usize) => r.val = n ⦄ := by
  have := UScalar.tryMk_eq .Usize n
  cases hm : (UScalar.tryMk .Usize n).match with
  | ok y =>
    rw [Result.match.isOk] at hm
    rw [hm]
    simp only [hm, Result.match.ok] at this
    simp only [WP.spec_ok, this.1]
  | vis e k =>
    rw [hm] at this
    cases e; simp only [UScalar.inBounds] at this; scalar_tac
  | div => rw [hm] at this; exact this.elim

/-- **Generic spec for `[Pt]::binary_search(&Pt { x, ZERO })`** (mirrors the Rust contract):
on `Ok j`, `s[j]` is *some* point with abscissa `x` (which one is unspecified); on `Err _`
and provided the slice is `SlotSorted`, no point has abscissa `x`. -/
theorem binary_search_Pt_spec_generic (s : Slice Pt) (g : GF16) :
    core.slice.Slice.binary_search Pt.Insts.CoreCmpOrd s { x := g, y := GF16.ZERO }
      ⦃ (r : core.result.Result Usize Usize) =>
      match r with
      | .Ok j => ∃ (h : j.val < s.length), (s.val[j.val]'h).x.value.val = g.value.val
      | .Err _ => PolyDecoder.SlotSorted s.val →
          ∀ p ∈ s.val, p.x.value.val ≠ g.value.val ⦄ := by
  unfold core.slice.Slice.binary_search
  apply WP.spec_bind (binarySearchAux_Pt_generic s.val g 0)
  intro r hr
  have hs := s.length_ineq
  cases r with
  | Ok j =>
    obtain ⟨_, hjl, hl⟩ := hr
    simp only [Nat.sub_zero] at hjl hl
    apply WP.spec_bind (usize_tryMk_spec j (by scalar_tac))
    intro j' hj'
    simp only [WP.spec_ok, Slice.length]
    exact ⟨hj' ▸ hjl, by simp only [hj']; exact hl⟩
  | Err j =>
    obtain ⟨hjl, hl⟩ := hr
    simp only [Nat.zero_add] at hjl
    apply WP.spec_bind (usize_tryMk_spec j (by scalar_tac))
    intro j' _
    simp only [WP.spec_ok]
    exact hl

/-- **`binary_search` on a `SlotSorted` slice computes `lookupY`**: on `Ok j`,
`lookupY = some s[j].y`; on `Err _`, `lookupY = none`.

This is the `lookupY` characterisation used by `decoded_message`.  It is *derived* from the
generic spec `binary_search_Pt_spec_generic` (which allows any matching index) together with
the uniqueness of the match under `SlotSorted` (`lookupY_eq_of_sorted`). -/
theorem binary_search_Pt_spec (s : Slice Pt) (g : GF16)
    (h_sorted : PolyDecoder.SlotSorted s.val) :
    core.slice.Slice.binary_search Pt.Insts.CoreCmpOrd s { x := g, y := GF16.ZERO }
      ⦃ (r : core.result.Result Usize Usize) =>
      match r with
      | .Ok j => ∃ (h : j.val < s.length),
          lookupY s.val g.value.val = some (s.val[j.val]'h).y
      | .Err _ => lookupY s.val g.value.val = none ⦄ := by
  apply WP.spec_mono (binary_search_Pt_spec_generic s g)
  intro r hr
  cases r with
  | Ok j =>
    obtain ⟨hj, hx⟩ := hr
    exact ⟨hj, lookupY_eq_of_sorted s.val g.value.val h_sorted j.val hj hx⟩
  | Err j =>
    exact lookupY_eq_none_of_forall s.val g.value.val (hr h_sorted)


end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder
