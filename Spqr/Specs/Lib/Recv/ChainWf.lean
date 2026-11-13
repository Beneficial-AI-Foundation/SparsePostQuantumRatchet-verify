/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Lib.ChainFrom
public import Spqr.Specs.Chain.Chain.Defs
import Spqr.Specs.Chain.Chain.New
public import Spqr.Specs.Chain.Chain.AddEpoch
import Spqr.Auxiliary.Aeneas.SpecImpExists
/-!
# Well-formedness of the chains built by `spqr::recv`

`recv` never receives a `Chain` value directly: every chain it manipulates is produced by
`chain_from` (i.e. by `Chain::from_pb` or `Chain::new`) and then threaded through
`Chain::recv_key` / `Chain::add_epoch` before being re-serialised with `Chain::into_pb`.

The contracts of `into_pb` and `recv_key` require the `links` deque to be *well formed* — its
live window `buf[head], …, buf[head+length-1]` must lie inside `buf`.  This file

* names that condition (`chainDequeWf`),
* shows that it holds for every chain `chain_from` returns (`chainDequeWf_of_chainFrom`), and
* shows that it is preserved by `recv_key` (`chainDequeWf_of_recvKeyPost`).

Together these discharge the deque preconditions of all chain sub-calls of `recv` from the
*inputs* of `recv` alone, so the top-level spec does not need to assume them.

It also names the remaining, genuinely input-dependent precondition of `recv_key`
(`recvKeyReady`): the per-epoch counter/bounds conditions of `recvKeyPre` for the target entry.
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr

/-- The live window of the `links` deque lies inside its buffer.  This is the precondition of
`Chain.into_pb_spec` (`hwf`) and of `Chain.recv_key_spec` (`h_wf`). -/
def chainDequeWf (c : chain.Chain) : Prop :=
  c.links.head.val + c.links.length.val ≤ c.links.buf.val.length

/-- The input-dependent preconditions of `Chain.recv_key_spec` for `(epoch, index)` on `c`:
the epoch distance fits a `usize`, and the targeted `ChainEpoch` entry (if the epoch is in
range) satisfies `recvKeyPre`. -/
def recvKeyReady (c : chain.Chain) (epoch : U64) (index : U32) : Prop :=
  (epoch.val ≤ c.current_epoch.val → c.current_epoch.val - epoch.val ≤ Usize.max) ∧
  (epoch.val ≤ c.current_epoch.val →
    c.current_epoch.val - epoch.val < c.links.length.val →
    match c.links.buf.val[c.links.head.val + chain.recvKeyIdx c epoch]? with
    | none => True
    | some ce => chain.recvKeyPre c.params index ce)

/-- Every chain returned by `chain_from` has a well-formed deque: `Chain::from_pb` builds it
with `head = 0` and `length = buf.length`, and `Chain::new` with a single entry. -/
theorem chainDequeWf_of_chainFrom (pb : Option proto.pq_ratchet.Chain)
    (vn : Option proto.pq_ratchet.pq_ratchet_state.VersionNegotiation) (c : chain.Chain)
    (h : chainFrom pb vn = ok (.Ok c)) : chainDequeWf c := by
  unfold chainDequeWf
  rcases pb with _ | pb1
  · rcases vn with _ | vn1
    · simp [chainFrom] at h
    · simp only [chainFrom, chainFromVersionNegotiation] at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · obtain ⟨r, hr, hpost⟩ :=
            WP.spec_imp_exists (chain.Chain.new_spec (alloc.vec.Vec.deref vn1.auth_key) _ _)
          rw [hr] at h
          obtain rfl := Result.ok_injective h
          simp only at hpost
          obtain ⟨-, -, -, -, -, -, hlen, hhead, hbuf⟩ := hpost
          split at hbuf
          · rename_i hl
            simp [hlen, hhead, hl]
          · exact hbuf.elim
  · simp only [chainFrom, ok.injEq] at h
    unfold chain.Chain.FunctionalModels.fromPb at h
    split at h
    · simp only [core.result.Result.Ok.injEq] at h
      subst h
      simp [Usize.ofNatCore_val_eq]
    · simp at h

/-- `recv_key` preserves deque well-formedness: either the chain is unchanged, or
`chainFrame` holds, which carries the bound explicitly. -/
theorem chainDequeWf_of_recvKeyPost (c c' : chain.Chain) (epoch : U64) (index : U32)
    (kr : core.result.Result (alloc.vec.Vec U8) Error)
    (hwf : chainDequeWf c) (hpost : chain.recvKeyPost c epoch index kr c') :
    chainDequeWf c' := by
  unfold chain.recvKeyPost at hpost
  split at hpost
  · exact hpost.2 ▸ hwf
  · obtain ⟨hout, hin⟩ := hpost
    by_cases hr : epoch.val ≤ c.current_epoch.val ∧
        c.current_epoch.val - epoch.val < c.links.length.val
    · exact (hin hr).1.2.2.2.2.2.2.2.2.1
    · have : epoch.val > c.current_epoch.val ∨
          c.current_epoch.val - epoch.val ≥ c.links.length.val := by omega
      exact (hout this).2 ▸ hwf

/-- The input-dependent preconditions of `Chain.add_epoch_spec` on `c` for `es`: the new epoch
is the successor of the current one, and the deque buffer can grow by one. -/
def addEpochReady (c : chain.Chain) (es : EpochSecret) : Prop :=
  es.epoch.val = c.current_epoch.val + 1 ∧ c.links.buf.val.length < Usize.max

/-- `add_epoch` preserves deque well-formedness: the head is unchanged, the length grows by
one, and the buffer grows by exactly one entry. -/
theorem chainDequeWf_of_addEpoch (c c' : chain.Chain) (es : EpochSecret)
    (hwf : chainDequeWf c) (hready : addEpochReady c es)
    (h : chain.Chain.add_epoch c es = ok c') : chainDequeWf c' := by
  obtain ⟨c'', h', hpost⟩ := WP.spec_imp_exists
    (chain.Chain.add_epoch_spec c es hready.1 (by unfold chainDequeWf at hwf; omega) hready.2)
  obtain rfl := Result.ok_injective (h'.symm.trans h)
  unfold chainDequeWf at hwf ⊢
  obtain ⟨-, -, -, -, -, -, hlen, hhead, hbuf⟩ := hpost
  split at hbuf <;> obtain ⟨ne, hb, -⟩ := hbuf <;> simp only [hb, List.length_append,
    List.length_singleton, hlen, hhead] <;> omega

end spqr
