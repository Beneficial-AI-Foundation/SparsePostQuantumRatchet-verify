/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.Defs

/-! # Chain definitions

Auxiliary definitions for `spqr.chain.Chain` specifications. -/

open Aeneas Aeneas.Std Result spqr crypto

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

/-- GC-related postconditions for the greater+valid-jump case of
`ChainEpochDirection.key`.  Separated for readability. -/
def keyPostGc (ced' : chain.ChainEpochDirection)
    (khPreGc : chain.KeyHistory) (max_ooo trim_threshold : Nat)
    (ctr_new : U32) : Prop :=
  (trim_threshold ≤ ced'.prev.data.length → max_ooo ≤ ctr_new.val →
     ∃ horizon : U32, horizon.val = ctr_new.val - max_ooo ∧
       (∀ m, m < ced'.prev.data.length ∧ m % 36 = 0 →
         Slice.lexCmpAux core.cmp.OrdU8
           (horizon.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8))
           (ced'.prev.data.val.slice m (m + 4)) ≠ ok .gt)) ∧
  (trim_threshold ≤ khPreGc.data.length → max_ooo ≤ ctr_new.val →
     ∃ horizon : U32, horizon.val = ctr_new.val - max_ooo ∧
       (∀ n, n < khPreGc.data.length ∧ n % 36 = 0 →
         Slice.lexCmpAux core.cmp.OrdU8
           (horizon.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8))
           (khPreGc.data.val.slice n (n + 4)) ≠ ok .gt →
         ∃ m, m < ced'.prev.data.length ∧ m % 36 = 0 ∧
           ced'.prev.data.val.slice m (m + 36) =
             khPreGc.data.val.slice n (n + 36))) ∧
  (khPreGc.data.length < trim_threshold → ced'.prev = khPreGc) ∧
  (trim_threshold ≤ khPreGc.data.length → max_ooo ≤ ctr_new.val →
     ∃ f : Nat → Nat,
       (∀ m, m < ced'.prev.data.length ∧ m % 36 = 0 →
         f m < khPreGc.data.length ∧ (f m) % 36 = 0 ∧
         ced'.prev.data.val.slice m (m + 36) =
           khPreGc.data.val.slice (f m) (f m + 36)) ∧
       (∀ m₁ m₂, m₁ < ced'.prev.data.length ∧ m₁ % 36 = 0 →
         m₂ < ced'.prev.data.length ∧ m₂ % 36 = 0 →
         f m₁ = f m₂ → m₁ = m₂)) ∧
  (trim_threshold ≤ khPreGc.data.length → max_ooo ≤ ctr_new.val →
     ∃ horizon : U32, horizon.val = ctr_new.val - max_ooo ∧
       ∃ g : Nat → Nat,
         (∀ n, n < khPreGc.data.length ∧ n % 36 = 0 →
           Slice.lexCmpAux core.cmp.OrdU8
             (horizon.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8))
             (khPreGc.data.val.slice n (n + 4)) ≠ ok .gt →
           g n < ced'.prev.data.length ∧ (g n) % 36 = 0 ∧
           ced'.prev.data.val.slice (g n) (g n + 36) =
             khPreGc.data.val.slice n (n + 36)) ∧
         (∀ n₁ n₂, n₁ < khPreGc.data.length ∧ n₁ % 36 = 0 →
           n₂ < khPreGc.data.length ∧ n₂ % 36 = 0 →
           Slice.lexCmpAux core.cmp.OrdU8
             (horizon.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8))
             (khPreGc.data.val.slice n₁ (n₁ + 4)) ≠ ok .gt →
           Slice.lexCmpAux core.cmp.OrdU8
             (horizon.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8))
             (khPreGc.data.val.slice n₂ (n₂ + 4)) ≠ ok .gt →
           g n₁ = g n₂ → n₁ = n₂))

/-- Precondition on the target chain-epoch entry for `recv_key` (64-bit). -/
def recvKeyPre (params : proto.pq_ratchet.ChainParams) (index : U32)
    (ce : chain.ChainEpoch) : Prop :=
  ce.recv.next.length = 32 ∧
  index.val ≤ U32.max - 390451572 ∧
  (chain.maxOoo params).val < 390451572 ∧
  ce.recv.ctr.val ≤ U32.max - 390451572 ∧
  ce.recv.prev.data.length + 36 * (index.val - ce.recv.ctr.val) ≤ Usize.max ∧
  ce.recv.ctr < U32.max ∧
  ce.recv.prev.data.length % 36 = 0 ∧
  ce.recv.prev.data.length ≤ 36 * ce.recv.ctr.val ∧
  index.val + (chain.maxOoo params).val ≤ U32.max ∧
  System.Platform.numBits = 64

/-- Precondition on the target chain-epoch entry for `recv_key` (32-bit). -/
def recvKeyPre32 (params : proto.pq_ratchet.ChainParams) (index : U32)
    (ce : chain.ChainEpoch) : Prop :=
  ce.recv.next.length = 32 ∧
  index.val ≤ U32.max - 108458770 ∧
  (chain.maxOoo params).val < 108458770 ∧
  ce.recv.ctr.val ≤ U32.max - 108458770 ∧
  ce.recv.prev.data.length + 36 * (index.val - ce.recv.ctr.val) ≤ Usize.max ∧
  ce.recv.ctr < U32.max ∧
  ce.recv.prev.data.length % 36 = 0 ∧
  ce.recv.prev.data.length ≤ 36 * ce.recv.ctr.val ∧
  index.val + (chain.maxOoo params).val ≤ U32.max

/-- Chain-level frame: scalar fields preserved, deque shape preserved,
only slot `phys` may differ. -/
def chainFrame (self self' : chain.Chain) (phys : Nat) : Prop :=
  self'.dir = self.dir ∧
  self'.current_epoch = self.current_epoch ∧
  self'.send_epoch = self.send_epoch ∧
  self'.next_root = self.next_root ∧
  self'.params = self.params ∧
  self'.links.head = self.links.head ∧
  self'.links.length = self.links.length ∧
  self'.links.buf.val.length = self.links.buf.val.length ∧
  self'.links.head.val + self'.links.length.val ≤ self'.links.buf.val.length ∧
  (∀ j, j ≠ phys → self'.links.buf.val[j]? = self.links.buf.val[j]?)

/-- Forward-advance sub-postcondition for `recv_key` case 4. -/
def recvKeyAdvancePost (self : chain.Chain) (index : U32)
    (ce ce' : chain.ChainEpoch)
    (result : core.result.Result (alloc.vec.Vec U8) Error) : Prop :=
  (∃ key : alloc.vec.Vec U8,
    result = core.result.Result.Ok key ∧
    key.length = 32 ∧
    key.val = (nextKeyHkdfOutput
      (chain.ChainEpochDirection.iterChainSecret ce.recv.next.val
        ce.recv.ctr.val (index.val - (ce.recv.ctr.val + 1)))
      ⟨index.val, by scalar_tac⟩).drop 32) ∧
  ce'.recv.ctr = index.val ∧
  ce'.recv.next.length = 32 ∧
  ce'.recv.next.val = (nextKeyHkdfOutput
    (chain.ChainEpochDirection.iterChainSecret ce.recv.next.val
      ce.recv.ctr.val (index.val - (ce.recv.ctr.val + 1)))
    ⟨index.val, by scalar_tac⟩).take 32 ∧
  ce'.recv.prev.data.length % 36 = 0 ∧
  ce'.recv.prev.data.length ≤
    ce.recv.prev.data.length + 36 * (index.val - ce.recv.ctr.val) ∧
  ce'.recv.prev.data.length ≤ Usize.max ∧
  (∃ (khPreGc : chain.KeyHistory) (mo tt : Nat) (cn : U32),
    mo = (chain.maxOoo self.params).val ∧
    tt = (mo * 11 / 10 + 1) * 36 ∧
    cn.val = index.val - 1 ∧
    ce'.recv.prev.data.length ≤ khPreGc.data.length ∧
    khPreGc.data.length % 36 = 0 ∧
    keyPostGc ce'.recv khPreGc mo tt cn)

/-- Per-entry postcondition for `recv_key`: relates old `ce`, new `ce'`,
and result across all four cases. -/
def recvKeyEpochPost (self : chain.Chain) (index : U32)
    (ce ce' : chain.ChainEpoch)
    (result : core.result.Result (alloc.vec.Vec U8) Error) : Prop :=
  ce'.send = ce.send ∧
  (index = ce.recv.ctr →
    result = core.result.Result.Err (Error.KeyAlreadyRequested index) ∧
    ce'.recv = ce.recv) ∧
  (index < ce.recv.ctr →
    ce'.recv.ctr = ce.recv.ctr ∧ ce'.recv.next = ce.recv.next ∧
    match result with
    | core.result.Result.Err e =>
        (e = Error.KeyTrimmed index ∧
          index + (chain.maxOoo self.params).val < ce.recv.ctr ∧
          ce'.recv.prev = ce.recv.prev) ∨
        (e = Error.KeyAlreadyRequested index ∧
          ce.recv.ctr ≤ index + (chain.maxOoo self.params).val ∧
          ce'.recv.prev = ce.recv.prev ∧
          (∀ k, k + 36 ≤ ce.recv.prev.data.length → k % 36 = 0 →
            ce.recv.prev.data.val.slice k (k + 4) ≠
              core.num.U32.to_be_bytes index))
    | core.result.Result.Ok out =>
        ce.recv.ctr ≤ index + (chain.maxOoo self.params).val ∧
        out.length = 32 ∧
        ce'.recv.prev.data.length = ce.recv.prev.data.length - 36 ∧
        ce'.recv.prev.data.length % 36 = 0 ∧
        (∃ off, off % 36 = 0 ∧
          off + 36 ≤ ce.recv.prev.data.length ∧
          ce.recv.prev.data.val.slice off (off + 4) =
            (core.num.U32.to_be_bytes index).val ∧
          (∀ k, k < off → k % 36 = 0 →
            ce.recv.prev.data.val.slice k (k + 4) ≠
              (core.num.U32.to_be_bytes index).val) ∧
          out = ce.recv.prev.data.val.slice (off + 4) (off + 36) ∧
          (∀ j, j < off →
            ce'.recv.prev.data[j]! = ce.recv.prev.data[j]!) ∧
          (off + 36 < ce.recv.prev.data.length →
            ce'.recv.prev.data = (ce.recv.prev.data.val.setSlice! off
              (ce.recv.prev.data.val.drop
                (ce.recv.prev.data.length - 36))).take
                  (ce.recv.prev.data.length - 36)) ∧
          (off + 36 = ce.recv.prev.data.length →
            ce'.recv.prev.data =
              ce.recv.prev.data.val.take off))) ∧
  (index > ce.recv.ctr →
    index.val - ce.recv.ctr.val > (chain.maxJump self.params).val →
    result = core.result.Result.Err
      (Error.KeyJump ce.recv.ctr index) ∧
    ce'.recv = ce.recv) ∧
  (index > ce.recv.ctr →
    index.val - ce.recv.ctr.val ≤ (chain.maxJump self.params).val →
    recvKeyAdvancePost self index ce ce' result)

/-- Total postcondition for `recv_key`: either the epoch is out of range
(error, chain unchanged) or the epoch is in range and the chain is updated
at exactly one slot with `recvKeyEpochPost`. -/
def recvKeyPost (self : chain.Chain) (epoch : U64) (index : U32)
    (result : core.result.Result (alloc.vec.Vec U8) Error)
    (self' : chain.Chain) : Prop :=
  let phys := self.links.head.val + recvKeyIdx self epoch
  (epoch.val > self.current_epoch.val ∨
   self.current_epoch.val - epoch.val ≥ self.links.length.val →
     result = core.result.Result.Err (Error.EpochOutOfRange epoch) ∧
     self' = self) ∧
  (epoch.val ≤ self.current_epoch.val ∧
   self.current_epoch.val - epoch.val < self.links.length.val →
     chainFrame self self' phys ∧
     match self.links.buf.val[phys]?, self'.links.buf.val[phys]? with
     | none, _ => False
     | some _, none => False
     | some ce, some ce' =>
       recvKeyEpochPost self index ce ce' result)

/-- Simplified per-entry postcondition for `recv_key` on 32-bit platforms.
Only constrains the result value, not the updated chain-epoch state. -/
def recvKeyEpochPost32 (self : chain.Chain) (index : U32)
    (ce : chain.ChainEpoch)
    (result : core.result.Result (alloc.vec.Vec U8) Error) : Prop :=
  (index = ce.recv.ctr →
    result = core.result.Result.Err (Error.KeyAlreadyRequested index)) ∧
  (index < ce.recv.ctr →
    match result with
    | core.result.Result.Err e =>
        (e = Error.KeyTrimmed index ∧
          index + (chain.maxOoo self.params).val < ce.recv.ctr) ∨
        (e = Error.KeyAlreadyRequested index ∧
          ce.recv.ctr ≤ index + (chain.maxOoo self.params).val ∧
          (∀ k, k + 36 ≤ ce.recv.prev.data.length → k % 36 = 0 →
            ce.recv.prev.data.val.slice k (k + 4) ≠
              core.num.U32.to_be_bytes index))
    | core.result.Result.Ok out =>
        ce.recv.ctr ≤ index + (chain.maxOoo self.params).val ∧
        out.length = 32 ∧
        (∃ off, off % 36 = 0 ∧
          off + 36 ≤ ce.recv.prev.data.length ∧
          ce.recv.prev.data.val.slice off (off + 4) =
            (core.num.U32.to_be_bytes index).val ∧
          (∀ k, k < off → k % 36 = 0 →
            ce.recv.prev.data.val.slice k (k + 4) ≠
              (core.num.U32.to_be_bytes index).val) ∧
          out = ce.recv.prev.data.val.slice (off + 4) (off + 36))) ∧
  (index > ce.recv.ctr →
    index.val - ce.recv.ctr.val > (chain.maxJump self.params).val →
    result = core.result.Result.Err
      (Error.KeyJump ce.recv.ctr index)) ∧
  (index > ce.recv.ctr →
    index.val - ce.recv.ctr.val ≤ (chain.maxJump self.params).val →
    match result with
    | core.result.Result.Ok key =>
        key.length = 32 ∧
        key.val = (nextKeyHkdfOutput
          (chain.ChainEpochDirection.iterChainSecret ce.recv.next.val
            ce.recv.ctr.val (index.val - (ce.recv.ctr.val + 1)))
          ⟨index.val, by scalar_tac⟩).drop 32
    | _ => False)

/-- Total postcondition for `recv_key` on 32-bit platforms. -/
def recvKeyPost32 (self : chain.Chain) (epoch : U64) (index : U32)
    (result : core.result.Result (alloc.vec.Vec U8) Error)
    (self' : chain.Chain) : Prop :=
  (epoch.val > self.current_epoch.val ∨
   self.current_epoch.val - epoch.val ≥ self.links.length.val →
     result = core.result.Result.Err (Error.EpochOutOfRange epoch) ∧
     self' = self) ∧
  (epoch.val ≤ self.current_epoch.val ∧
   self.current_epoch.val - epoch.val < self.links.length.val →
     self'.dir = self.dir ∧
     self'.current_epoch = self.current_epoch ∧
     self'.send_epoch = self.send_epoch ∧
     self'.next_root = self.next_root ∧
     self'.params = self.params ∧
     let phys := self.links.head.val + recvKeyIdx self epoch
     match self.links.buf.val[phys]? with
     | none => False
     | some ce => recvKeyEpochPost32 self index ce result)

/-- Per-slot postcondition for the target element after `send_key` succeeds. -/
def sendKeySlotPost (ce ce' : chain.ChainEpoch) (i : U32)
    (key : alloc.vec.Vec U8) : Prop :=
  i.val = ce.send.ctr.val + 1 ∧
  key.length = 32 ∧
  key.val = (nextKeyHkdfOutput ce.send.next i).drop 32 ∧
  ce'.recv = ce.recv ∧
  ce'.send.ctr = i ∧
  ce'.send.next.length = ce.send.next.length ∧
  ce'.send.next.val = (nextKeyHkdfOutput ce.send.next i).take 32 ∧
  ce'.send.prev = ce.send.prev

/-- Deque-shape postcondition for `send_key` success: how the deque head, length, and buffer
change relative to `idx` and `ei`. -/
def sendKeyDequePost (self self' : chain.Chain) (idx ei phys : Nat) : Prop :=
  self'.links.head.val = self.links.head.val + (idx - ei) ∧
  self'.links.length.val = self.links.length.val - (idx - ei) ∧
  self'.links.buf.val.length = self.links.buf.val.length ∧
  self'.links.head.val + self'.links.length.val ≤ self'.links.buf.val.length ∧
  ei < self'.links.length.val ∧
  (self.send_epoch = self'.send_epoch →
    self'.links.head = self.links.head ∧
    self'.links.length = self.links.length ∧
    ∀ j, j ≠ phys →
      self'.links.buf.val[j]? = self.links.buf.val[j]?) ∧
  (self.send_epoch ≠ self'.send_epoch →
    ∀ j, self.links.head.val + (idx - ei) ≤ j → j < phys →
      clearedAt self.links self'.links j) ∧
  (∀ j, (j < self.links.head.val + (idx - ei) ∨ phys < j) →
    self'.links.buf.val[j]? = self.links.buf.val[j]?)

/-- Total postcondition for `send_key`.

• `epoch < send_epoch` → `Err SendKeyEpochDecreased`, chain unchanged.
• `epoch` out of range → `Err EpochOutOfRange`, chain unchanged.
• Otherwise → `Ok (i, key)` with the target slot updated and the deque possibly trimmed/cleared. -/
def sendKeyPost (self : chain.Chain) (epoch : U64)
    (result : core.result.Result (U32 × alloc.vec.Vec U8) Error)
    (self' : chain.Chain) : Prop :=
  (epoch.val < self.send_epoch.val →
    result = core.result.Result.Err (Error.SendKeyEpochDecreased self.send_epoch epoch) ∧
    self' = self) ∧
  (self.send_epoch.val ≤ epoch.val →
    (epoch.val > self.current_epoch.val ∨
     self.current_epoch.val - epoch.val ≥ self.links.length.val) →
      result = core.result.Result.Err (Error.EpochOutOfRange epoch) ∧
      self' = self) ∧
  (self.send_epoch.val ≤ epoch.val →
    epoch.val ≤ self.current_epoch.val →
    self.current_epoch.val - epoch.val < self.links.length.val →
      let idx := sendKeyIdx self epoch
      let ei := sendKeyEi self epoch
      let phys := self.links.head.val + idx
      self'.dir = self.dir ∧
      self'.current_epoch = self.current_epoch ∧
      self'.send_epoch = epoch ∧
      self'.next_root = self.next_root ∧
      self'.params = self.params ∧
      sendKeyDequePost self self' idx ei phys ∧
      match self.links.buf.val[phys]?, self'.links.buf.val[phys]? with
      | some ce, some ce' =>
        ∃ i : U32, ∃ key : alloc.vec.Vec U8,
          result = core.result.Result.Ok (i, key) ∧
          sendKeySlotPost ce ce' i key
      | _, _ => False)

end spqr.chain
