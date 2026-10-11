/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.ChainEpochDirection.IntoPb
import Spqr.Specs.Chain.Chain.FunctionalModels

/-! # Spec theorem for `spqr::chain::{spqr::chain::Chain}::into_pb`

Converts a `Chain` from the in-memory Rust form (`chain.Chain`) into the protobuf form
(`proto.pq_ratchet.Chain`) used for saving it to disk. The `current_epoch`, `send_epoch`,
`next_root` fields are copied verbatim, `params` is wrapped in `some`, `direction` is
converted via `directionToI32`, and `links` are produced by popping each live `ChainEpoch`
from the front of the deque and pushing its conversion (`ChainEpochDirection::into_pb` on its
`send` and `recv` fields) onto a `Vec` (`into_pb_loop`).
The reverse direction is `from_pb`.

**Source**: spqr/src/chain.rs (lines 425:4-442:5)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain.into_pb_loop

/-- **Spec theorem for `spqr.chain.Chain.into_pb_loop.body`**:
One iteration of the link-conversion loop. If the deque is empty the loop stops and returns
`links` unchanged; otherwise the front element `buf[head]` is popped (`head` advances,
`length` decreases, `buf` is unchanged) and its conversion `epochIntoPb` is appended to
`links`. -/
@[step]
theorem body_spec
    (chain_links : alloc.collections.vec_deque.VecDeque chain.ChainEpoch Global)
    (links : alloc.vec.Vec proto.pq_ratchet.chain.Epoch)
    (hwf : chain_links.head.val + chain_links.length.val ≤ chain_links.buf.val.length)
    (hcap : links.val.length + chain_links.length.val ≤ Usize.max) :
    body chain_links links ⦃ cf =>
      match cf with
      | .done r => chain_links.length.val = 0 ∧ r = links
      | .cont (d, links') =>
          ∃ h : chain_links.head.val < chain_links.buf.val.length,
          chain_links.length.val ≠ 0 ∧ d.buf = chain_links.buf ∧
          d.head.val = chain_links.head.val + 1 ∧
          d.length.val = chain_links.length.val - 1 ∧
          links'.val = links.val ++
            [FunctionalModels.epochIntoPb (chain_links.buf.val[chain_links.head.val]'h)] ⦄ := by
  unfold body alloc.collections.vec_deque.VecDeque.pop_front
  split
  · simp_all
  · have hidx : chain_links.head < chain_links.buf.length := by scalar_tac
    simp only [dif_pos hidx]
    step*
    refine ⟨hidx, by scalar_tac, by scalar_tac, by scalar_tac, ?_⟩
    simp only [FunctionalModels.epochIntoPb, *]

end spqr.chain.Chain.into_pb_loop

namespace spqr.chain.Chain

private theorem take_drop_succ {α : Type} (l : List α) (h n : Nat) (hh : h < l.length) :
    (l.drop h).take (n + 1) = l[h] :: (l.drop (h + 1)).take n := by
  rw [List.drop_eq_getElem_cons hh, List.take_succ_cons]

/-- **Spec theorem for `spqr.chain.Chain.into_pb_loop`**:
Starting from a well-formed deque `chain_links` and an accumulator `links` with enough room,
the loop returns `links` followed by the conversions (`epochIntoPb`) of the live elements of
`chain_links`, in order. -/
@[step]
theorem into_pb_loop_spec
    (chain_links : alloc.collections.vec_deque.VecDeque chain.ChainEpoch Global)
    (links : alloc.vec.Vec proto.pq_ratchet.chain.Epoch)
    (hwf : chain_links.head.val + chain_links.length.val ≤ chain_links.buf.val.length)
    (hcap : links.val.length + chain_links.length.val ≤ Usize.max) :
    into_pb_loop chain_links links ⦃ (r : alloc.vec.Vec proto.pq_ratchet.chain.Epoch) =>
      r.val = links.val ++
        (FunctionalModels.dequeContents chain_links).map FunctionalModels.epochIntoPb ⦄ := by
  generalize hn : chain_links.length.val = n at hwf hcap
  induction n generalizing chain_links links with
  | zero =>
    unfold into_pb_loop
    rw [loop]
    apply WP.spec_bind (into_pb_loop.body_spec chain_links links (by omega) (by omega))
    rintro (⟨d, links'⟩ | r) hcf
    · obtain ⟨_, hne, _⟩ := hcf
      omega
    · obtain ⟨_, rfl⟩ := hcf
      simp [FunctionalModels.dequeContents, hn]
  | succ n ih =>
    unfold into_pb_loop
    rw [loop]
    apply WP.spec_bind (into_pb_loop.body_spec chain_links links (by omega) (by omega))
    rintro (⟨d, links'⟩ | r) hcf
    · obtain ⟨hidx, _, hbuf, hhead, hlen, hlinks⟩ := hcf
      have := ih d links' (by omega) (by rw [hbuf]; omega)
        (by simp only [hlinks, List.length_append, List.length_singleton]; omega)
      unfold into_pb_loop at this
      apply WP.spec_mono this
      intro r hr
      rw [hr, hlinks]
      simp only [FunctionalModels.dequeContents, hn, hbuf, hhead, hlen,
        take_drop_succ _ _ _ hidx, List.map_cons, List.append_assoc, List.singleton_append,
        Nat.add_sub_cancel]
    · obtain ⟨_, _⟩ := hcf
      omega

/-- **Spec theorem for `spqr.chain.Chain.into_pb`**:
• Succeeds (no panic) whenever the `links` deque is well-formed, i.e. its live window
  `buf[head], …, buf[head+length-1]` lies inside `buf`.
• The result is exactly the functional model `FunctionalModels.intoPb self`.
**Source**: spqr/src/chain.rs (lines 425:4-442:5) -/
@[step]
theorem into_pb_spec (self : chain.Chain)
    (hwf : self.links.head.val + self.links.length.val ≤ self.links.buf.val.length) :
    into_pb self ⦃ (result : proto.pq_ratchet.Chain) =>
      result = FunctionalModels.intoPb self ⦄ := by
  unfold into_pb FunctionalModels.intoPb
  step*
  · simp only [alloc.vec.Vec.with_capacity, alloc.vec.Vec.from_val, List.length_nil, zero_add]
    scalar_tac
  · unfold I32.Insts.CoreConvertFromDirection.from
    cases self.dir <;> simp only [FunctionalModels.directionToI32, read_discriminant] <;>
      simp only [bind_ok, WP.spec_ok, proto.pq_ratchet.Chain.mk.injEq, and_self, and_true,
        true_and] <;> refine ⟨by decide, ?_⟩ <;> apply alloc.vec.Vec.ext <;>
      simpa [alloc.vec.Vec.with_capacity] using ‹_›

end spqr.chain.Chain
