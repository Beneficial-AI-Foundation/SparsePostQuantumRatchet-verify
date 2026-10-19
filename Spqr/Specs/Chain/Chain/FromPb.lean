/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
import Spqr.Auxiliary.Aeneas.Result
import Spqr.Specs.Chain.ChainEpochDirection.FromPb
public import Spqr.Specs.Chain.Chain.FunctionalModels
import Spqr.Specs.Proto.PqRatchet.Direction.TryFrom

/-! # Spec theorem for `spqr::chain::{spqr::chain::Chain}::from_pb`

Converts a `Chain` from the protobuf form (`proto.pq_ratchet.Chain`) back into the
in-memory Rust form (`chain.Chain`). The `direction` is decoded via `directionFromI32`,
`links` are converted one by one by the nested `link_from_pb` (`ChainEpochDirection.from_pb`
on each epoch's `send`/`recv` fields) and pushed into a fresh `VecDeque` (`from_pb_loop`,
stopping at the first error), and `params` is unwrapped from `Option`. The reverse direction
is `into_pb`.

**Source**: spqr/src/chain.rs (lines 445:4-475:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain

/-- A computation whose spec pins down its result is `ok` of that result. -/
private theorem eq_ok_of_spec {α : Type} {x : Result α} {a : α} (h : x ⦃ v => v = a ⦄) :
    x = ok a := by
  cases x <;> simp_all [WP.spec_ok, WP.spec_vis, WP.spec_div]

/-- **Spec theorem for `spqr.chain.Chain.from_pb.link_from_pb`**:
never panics; the result is the functional model `FunctionalModels.epochFromPb link`. -/
@[step]
theorem from_pb.link_from_pb_spec (link : proto.pq_ratchet.chain.Epoch) :
    from_pb.link_from_pb link ⦃ (r : core.result.Result chain.ChainEpoch Error) =>
      r = FunctionalModels.epochFromPb link ⦄ := by
  have hd : ∀ x, chain.ChainEpochDirection.from_pb x =
      ok (chain.ChainEpochDirection.FunctionalModels.fromPb x) :=
    fun x => eq_ok_of_spec (chain.ChainEpochDirection.from_pb_spec x)
  have hdir : ∀ x, (∃ d, chain.ChainEpochDirection.FunctionalModels.fromPb x = .Ok d) ∨
      chain.ChainEpochDirection.FunctionalModels.fromPb x = .Err .StateDecode := by
    intro x
    rcases h : chain.ChainEpochDirection.FunctionalModels.fromPb x with d | e
    · exact .inl ⟨d, rfl⟩
    · exact .inr (by rw [chain.ChainEpochDirection.FunctionalModels.fromPb_err x e h])
  obtain ⟨_ | s, _ | r⟩ := link <;>
    simp only [from_pb.link_from_pb, FunctionalModels.epochFromPb, hd,
      _root_.core.option.Option.ok_or, bind_ok, Option.map,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
  · simp
  · simp
  · rcases hdir s with ⟨sd, hs⟩ | hs <;> simp [hs]
  · rcases hdir s with ⟨sd, hs⟩ | hs <;> rcases hdir r with ⟨rd, hr⟩ | hr <;> simp [hs, hr]

/-- The only error `traverseResult epochFromPb` can return is `Error::StateDecode`. -/
private theorem traverseResult_epochFromPb_err (l : List proto.pq_ratchet.chain.Epoch)
    (e : Error) (h : FunctionalModels.traverseResult FunctionalModels.epochFromPb l = .Err e) :
    e = .StateDecode := by
  have hep : ∀ x e', FunctionalModels.epochFromPb x = .Err e' → e' = .StateDecode := by
    intro x e' hx
    unfold FunctionalModels.epochFromPb at hx
    split at hx <;> cases hx; rfl
  induction l with
  | nil => simp [FunctionalModels.traverseResult] at h
  | cons a tl ih =>
    simp only [FunctionalModels.traverseResult] at h
    split at h
    · cases h; exact hep a _ ‹_›
    · split at h
      · cases h; exact ih ‹_›
      · cases h

/-- `IntoIter::next` on the Aeneas model (`IntoIter T` is a plain `def` for `Vec T`, so its
equations do not simplify well; this states the two cases once). -/
private theorem into_iter_next_spec {T : Type} (it : alloc.vec.into_iter.IntoIter T) :
    alloc.vec.into_iter.IteratorIntoIter.next it ⦃ (o, it') =>
      match it.val with
      | [] => o = none ∧ it' = it
      | hd :: tl => o = some hd ∧ it'.val = tl ⦄ := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split <;> refine (WP.spec_ok _).mpr ?_ <;> simp only [*] <;> exact ⟨rfl, by simp⟩

/-- **Spec theorem for `spqr.chain.Chain.from_pb_loop.body`**. -/
@[step]
theorem from_pb_loop.body_spec
    (iter : alloc.vec.into_iter.IntoIter proto.pq_ratchet.chain.Epoch)
    (links : alloc.collections.vec_deque.VecDeque chain.ChainEpoch Global)
    (hcap : links.buf.val.length + iter.val.length ≤ Usize.max)
    (hlen : links.length.val = links.buf.val.length) :
    from_pb_loop.body iter links ⦃ cf =>
      match cf with
      | .done (res, err) =>
          match iter.val with
          | [] => res = links ∧ err = none
          | link :: _ => ∃ e, FunctionalModels.epochFromPb link = .Err e ∧ err = some e
      | .cont (iter', links') =>
          ∃ link ce, iter.val = link :: iter'.val ∧
            FunctionalModels.epochFromPb link = .Ok ce ∧
            links'.buf.val = links.buf.val ++ [ce] ∧ links'.head = links.head ∧
            links'.length.val = links'.buf.val.length ⦄ := by
  unfold from_pb_loop.body
  apply WP.spec_bind (into_iter_next_spec iter)
  rintro ⟨o, it'⟩ hnext
  rcases hv : iter.val with _ | ⟨hd, tl⟩ <;> rw [hv] at hnext <;> obtain ⟨rfl, h_it'⟩ := hnext
  · simp_all
  · step*
    simp_all

end spqr.chain.Chain

namespace spqr.chain.Chain

/-- **Spec theorem for `spqr.chain.Chain.from_pb_loop`**: the loop converts the remaining
links in order; on success it returns no error and appends the converted epochs to `links`,
otherwise it returns the first error. -/
@[step]
theorem from_pb_loop_spec
    (iter : alloc.vec.into_iter.IntoIter proto.pq_ratchet.chain.Epoch)
    (links : alloc.collections.vec_deque.VecDeque chain.ChainEpoch Global)
    (hcap : links.buf.val.length + iter.val.length ≤ Usize.max)
    (hlen : links.length.val = links.buf.val.length) :
    from_pb_loop iter links ⦃ res =>
      match FunctionalModels.traverseResult FunctionalModels.epochFromPb iter.val with
      | .Ok l => res.2 = none ∧ res.1.buf.val = links.buf.val ++ l ∧
          res.1.head = links.head ∧ res.1.length.val = res.1.buf.val.length
      | .Err e => res.2 = some e ⦄ := by
  generalize hl : iter.val = l at hcap
  induction l generalizing iter links with
  | nil =>
    unfold from_pb_loop
    rw [loop]
    apply WP.spec_bind (from_pb_loop.body_spec iter links (by rw [hl]; exact hcap) hlen)
    rintro (⟨it', links'⟩ | ⟨res, err⟩) hcf
    · obtain ⟨_, _, hit, _⟩ := hcf
      rw [hl] at hit
      cases hit
    · simp only [hl] at hcf
      obtain ⟨rfl, rfl⟩ := hcf
      simp [FunctionalModels.traverseResult, hlen]
  | cons a tl ih =>
    unfold from_pb_loop
    rw [loop]
    apply WP.spec_bind (from_pb_loop.body_spec iter links (by rw [hl]; exact hcap) hlen)
    rintro (⟨it', links'⟩ | ⟨res, err⟩) hcf
    · obtain ⟨link, ce, hit, hce, hbuf, hhead, hlen'⟩ := hcf
      rw [hl] at hit
      obtain ⟨rfl, htl⟩ := List.cons.inj hit
      have := ih it' links' hlen' htl.symm (by rw [hbuf]; simp only [List.length_append,
        List.length_cons, List.length_nil] at hcap ⊢; omega)
      unfold from_pb_loop at this
      apply WP.spec_mono this
      rintro ⟨res, err⟩ hr
      simp only [FunctionalModels.traverseResult, hce]
      split at hr
      · simp_all
      · simp_all
    · simp only [hl] at hcf
      obtain ⟨e, he, rfl⟩ := hcf
      simp [FunctionalModels.traverseResult, he]

private theorem traverseVec_of_ok {α β : Type} (f : α → core.result.Result β Error)
    (v : alloc.vec.Vec α) (l : List β) (h : FunctionalModels.traverseResult f v.val = .Ok l) :
    ∃ hl, FunctionalModels.traverseVec f v = .Ok (alloc.vec.Vec.from l hl) := by
  refine ⟨FunctionalModels.traverseResult_length f v.val l h ▸ v.property, ?_⟩
  unfold FunctionalModels.traverseVec
  split
  · simp_all
  · rename_i l' hl'
    rw [h, core.result.Result.Ok.injEq] at hl'
    subst hl'
    rfl

private theorem traverseVec_of_err {α β : Type} (f : α → core.result.Result β Error)
    (v : alloc.vec.Vec α) (e : Error) (h : FunctionalModels.traverseResult f v.val = .Err e) :
    FunctionalModels.traverseVec f v = .Err e := by
  unfold FunctionalModels.traverseVec
  split
  · simp_all
  · simp_all

/-- **Spec theorem for `spqr.chain.Chain.from_pb`**:
• The call always succeeds (no panic): the direction decode, every epoch conversion and the
  `params` unwrap can only produce `Err StateDecode`, never a panic.
• The result is exactly the functional model `FunctionalModels.fromPb pb`.
**Source**: spqr/src/chain.rs (lines 445:4-475:5) -/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.Chain) :
    from_pb pb ⦃ (result : core.result.Result chain.Chain Error) =>
      result = FunctionalModels.fromPb pb ⦄ := by
  unfold from_pb FunctionalModels.fromPb
  apply WP.spec_bind
    (proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from_spec _)
  intro r hr
  have hr' : r = match FunctionalModels.directionFromI32 pb.direction with
      | .Ok d => .Ok d
      | .Err _ => .Err pb.direction := by
    rw [hr]
    unfold FunctionalModels.directionFromI32
    split <;> split <;> simp_all
  subst hr'
  rcases hd : FunctionalModels.directionFromI32 pb.direction with dir | e
  · simp only [_root_.core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch,
      bind_ok, alloc.collections.vec_deque.VecDequeTGlobal.new,
      alloc.vec.IntoIteratorVec.into_iter]
    apply WP.spec_bind_ok
    apply WP.spec_bind (from_pb_loop_spec pb.links _ (by simp) (by simp))
    rintro ⟨links1, err⟩ hpost
    rcases ht : FunctionalModels.traverseResult FunctionalModels.epochFromPb pb.links.val with
      l | e
    · rw [ht] at hpost
      obtain ⟨rfl, hbuf, hhead, hlen⟩ := hpost
      obtain ⟨hl, hv⟩ := traverseVec_of_ok _ _ _ ht
      rw [hv]
      rcases hp : pb.params with _ | params
      · simp [_root_.core.option.Option.ok_or,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
      · simp only [_root_.core.option.Option.ok_or, bind_ok]
        simp only at hbuf hhead hlen
        obtain ⟨buf, head, len⟩ := links1
        have hbv : buf = alloc.vec.Vec.from l hl := by
          apply alloc.vec.Vec.ext
          simpa [alloc.vec.Vec.new] using hbuf
        subst hbv
        simp only at hhead hlen
        subst hhead
        apply (WP.spec_ok _).mpr
        congr 3
        apply UScalar.eq_of_val_eq
        simp [hlen]
    · rw [ht] at hpost
      simp only at hpost
      subst hpost
      rw [traverseVec_of_err _ _ _ ht, traverseResult_epochFromPb_err _ _ ht]
      simp
  · simp only [_root_.core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch,
      bind_ok, from_pb.closure.Insts.CoreOpsFunctionFnOnceTupleUnknownEnumValueError.call_once,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]

end spqr.chain.Chain
