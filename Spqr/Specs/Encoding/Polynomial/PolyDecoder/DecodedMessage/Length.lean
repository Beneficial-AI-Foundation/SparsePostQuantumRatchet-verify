/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import SrcTranslated.Funs
import Spqr.Auxiliary.Aeneas.Loop
import Spqr.Auxiliary.Aeneas.SpecImpExists
import Spqr.Auxiliary.Aeneas.StdNextStepUsize
import Spqr.Auxiliary.Aeneas.Vec

/-! # Length of the message that `decoded_message` returns

A completed message has two bytes per point that the decoder needs. Unlike
`decoded_message_spec`, this needs no `PointsValid` premise: it follows from success alone. -/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder

/-- A completed message has two bytes per point the decoder needs. -/
theorem decoded_message_length {d : encoding.polynomial.PolyDecoder} {m : alloc.vec.Vec Std.U8}
    (h : encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message d =
      ok (some m)) :
    m.val.length = 2 * d.pts_needed.val := by
  simp only [encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message] at h
  split at h
  · simp only [ok.injEq, reduceCtorEq] at h
  simp only [Result.bind_eq_ok] at h
  obtain ⟨_, -, rn, -, h⟩ := h
  split at h
  · simp only [ok.injEq, reduceCtorEq] at h
  simp only [Result.bind_eq_ok] at h
  obtain ⟨polys, -, i1, -, out1, hl, h⟩ := h
  simp only [Result.ok.injEq, Option.some.injEq] at h
  subst h
  simp only [encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message_loop1]
    at hl
  refine loop_ok_post (fun x => x.1.end.val - x.1.start.val)
    (fun x => x.2.2.val.length = 2 * x.1.start.val ∧ x.1.start.val ≤ x.1.end.val ∧
      x.1.end = d.pts_needed)
    (fun y => y.val.length = 2 * d.pts_needed.val) _ ?_ _ _
    ⟨by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new], by simp, rfl⟩ hl
  rintro ⟨iter, polys0, out⟩ r ⟨hlen, hle, hend⟩ hr
  simp only at hlen hle hend
  simp only [encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message_loop1.body,
    Result.bind_eq_ok] at hr
  obtain ⟨⟨o, iter1⟩, hn, hr⟩ := hr
  have hns := WP.post_of_ok (core.iter.range.IteratorRange.next_spec iter) hn
  cases o with
  | none =>
    simp only [alloc.vec.Vec.index_slice_index, core.option.Option.is_none,
        Option.isNone_iff_eq_none, Slice.index_SliceIndexRangeToUsizeSliceInst, UScalar.lt_equiv,
        UScalar.ofNatCore_val_eq, uncurry_apply_pair, ok.injEq] at hr
    subst hr
    have : ¬ iter.start.val < iter.end.val := fun hc => absurd (hns.2 hc).1 (by simp)
    simp only
    rw [hlen, ← hend]; omega
  | some i =>
    have hlt : iter.start.val < iter.end.val := by
      by_contra hc; exact absurd (hns.1 hc).1 (by simp)
    obtain ⟨-, hs1, he1⟩ := hns.2 hlt
    simp only [alloc.vec.Vec.index_slice_index, core.option.Option.is_none,
        Option.isNone_iff_eq_none, Slice.index_SliceIndexRangeToUsizeSliceInst, UScalar.lt_equiv,
        UScalar.ofNatCore_val_eq, uncurry_apply_pair] at hr
    simp only [Result.bind_eq_ok] at hr
    obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, ⟨polys1, y⟩, -, hr⟩ := hr
    simp only [uncurry_apply_pair] at hr
    simp only [Result.bind_eq_ok] at hr
    obtain ⟨_, -, _, -, o1, hp1, _, -, o2, hp2, hr⟩ := hr
    simp only [Result.ok.injEq] at hr
    subst hr
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simp only
      rw [alloc.vec.Vec.push_ok_length hp2, alloc.vec.Vec.push_ok_length hp1, hlen, hs1]; ring
    · simp only; rw [hs1, he1]; omega
    · simp only; rw [he1, hend]
    · simp only; rw [he1, hs1]; omega

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder
