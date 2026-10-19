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
  `x` only): the `y` of the first point whose `x` equals the target, or `none`.
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

/-! ## `binary_search` on `Pt` lists computes `lookupY` -/

/-- `Slice.binarySearchAux` with the `Pt` ordering: `Ok j` means the point at
position `j - i` has abscissa `x` and `lookupY` returns its ordinate; `Err _` means
`lookupY` returns `none`. -/
theorem binarySearchAux_Pt (l : List Pt) (g : GF16) (i : Nat) :
    Slice.binarySearchAux Pt.Insts.CoreCmpOrd l { x := g, y := GF16.ZERO } i
      ⦃ (r : core.result.Result Nat Nat) =>
      match r with
      | .Ok j => i ≤ j ∧ ∃ (h : j - i < l.length),
          lookupY l g.value.val = some (l[j - i]'h).y
      | .Err j => j ≤ i + l.length ∧ lookupY l g.value.val = none ⦄ := by
  induction l generalizing i with
  | nil => simp [Slice.binarySearchAux, lookupY]
  | cons p rest ih =>
    simp only [Slice.binarySearchAux]
    have hcmp := spqr.encoding.polynomial.Pt.Insts.CoreCmpOrd.cmp_spec p { x := g, y := GF16.ZERO }
    apply WP.spec_bind hcmp
    intro o ho
    simp only at ho
    subst ho
    rcases Nat.lt_trichotomy p.x.value.val g.value.val with hlt | heq | hgt
    · rw [Nat.compare_eq_lt.mpr hlt]
      apply WP.spec_mono (ih (i + 1))
      intro r hr
      cases r with
      | Ok j =>
        obtain ⟨hij, hjl, hl⟩ := hr
        refine ⟨by omega, ?_⟩
        simp only [lookupY, hlt, ite_true, List.length_cons]
        refine ⟨by omega, ?_⟩
        rw [hl]
        have : j - i = (j - (i + 1)) + 1 := by omega
        simp [this]
      | Err j =>
        simp only [lookupY, hlt, ite_true, List.length_cons]
        exact ⟨by omega, hr.2⟩
    · rw [Nat.compare_eq_eq.mpr heq]
      simp only [WP.spec_ok]
      refine ⟨le_refl _, by simp, ?_⟩
      simp [lookupY, heq]
    · rw [Nat.compare_eq_gt.mpr hgt]
      simp only [WP.spec_ok]
      refine ⟨by simp, ?_⟩
      simp [lookupY, Nat.lt_asymm hgt, Nat.ne_of_gt hgt]

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

/-- `[Pt]::binary_search(&Pt { x, ZERO })` on a slice with `x`-value `x`:
on `Ok j`, `lookupY = some s[j].y`; on `Err _`, `lookupY = none`. -/
theorem binary_search_Pt_spec (s : Slice Pt) (g : GF16) :
    core.slice.Slice.binary_search Pt.Insts.CoreCmpOrd s { x := g, y := GF16.ZERO }
      ⦃ (r : core.result.Result Usize Usize) =>
      match r with
      | .Ok j => ∃ (h : j.val < s.length),
          lookupY s.val g.value.val = some (s.val[j.val]'h).y
      | .Err _ => lookupY s.val g.value.val = none ⦄ := by
  unfold core.slice.Slice.binary_search
  apply WP.spec_bind (binarySearchAux_Pt s.val g 0)
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

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder
