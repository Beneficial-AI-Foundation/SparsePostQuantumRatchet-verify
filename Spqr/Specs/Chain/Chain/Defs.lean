/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-! # Chain definitions

Auxiliary definitions for `spqr.chain.Chain` specifications. -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain

/-- Slot `j` is *cleared*: element exists in both deques, `recv`/`send.ctr`/`send.prev` unchanged,
`send.next` emptied. -/
def clearedAt (vd vd' : alloc.collections.vec_deque.VecDeque chain.ChainEpoch Global)
    (j : Nat) : Prop :=
  ∃ ce ce' : chain.ChainEpoch,
    vd.buf.val[j]? = some ce ∧
    vd'.buf.val[j]? = some ce' ∧
    ce'.recv = ce.recv ∧
    ce'.send.next.val = [] ∧
    ce'.send.ctr = ce.send.ctr ∧
    ce'.send.prev = ce.send.prev

/-- Deque index from `epoch_idx`: `links.len() - 1 - (current_epoch - epoch)`. -/
def sendKeyIdx (self : chain.Chain) (epoch : U64) : Nat :=
  self.links.length.val - 1 - (self.current_epoch.val - epoch.val)

/-- The deque index of the epoch whose key is derived, *after* the trimming loop: unchanged when
the send epoch does not move, and `min idx EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH` otherwise. -/
def sendKeyEi (self : chain.Chain) (epoch : U64) : Nat :=
  if self.send_epoch = epoch then sendKeyIdx self epoch
  else min (sendKeyIdx self epoch) chain.EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH.val

/-- The deque index for `recv_key`: `links.len() - 1 - (current_epoch - epoch)`. -/
def recvKeyIdx (self : chain.Chain) (epoch : U64) : Nat :=
  self.links.length.val - 1 - (self.current_epoch.val - epoch.val)

end spqr.chain
