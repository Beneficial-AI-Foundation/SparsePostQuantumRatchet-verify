/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.Defs
import Spqr.Specs.Chain.KeyHistory.Defs

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

/-- Postcondition for the less-than case of `ChainEpochDirection.key`:
`ats < self.ctr`, delegates to `KeyHistory.get`. -/
def cedKeyLessPost (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (result : core.result.Result (alloc.vec.Vec U8) Error)
    (self' : chain.ChainEpochDirection) : Prop :=
  self'.ctr = self.ctr ∧
  self'.next = self.next ∧
  match result with
  | core.result.Result.Err e =>
      (e = Error.KeyTrimmed ats ∧
        ats + (chain.maxOoo params).val < self.ctr ∧
        self'.prev = self.prev) ∨
      (e = Error.KeyAlreadyRequested ats ∧
        self.ctr ≤ ats + (chain.maxOoo params).val ∧
        self'.prev = self.prev ∧
        (∀ k, k + 36 ≤ self.prev.data.length → k % 36 = 0 →
          self.prev.data.val.slice k (k + 4) ≠ core.num.U32.to_be_bytes ats))
  | core.result.Result.Ok out =>
      self.ctr ≤ ats + (chain.maxOoo params).val ∧
      out.length = 32 ∧
      self'.prev.data.length = self.prev.data.length - 36 ∧
      self'.prev.data.length % 36 = 0 ∧
      (∃ off, off % 36 = 0 ∧
        off + 36 ≤ self.prev.data.length ∧
        self.prev.data.val.slice off (off + 4) = (core.num.U32.to_be_bytes ats).val ∧
        (∀ k, k < off → k % 36 = 0 →
          self.prev.data.val.slice k (k + 4) ≠ (core.num.U32.to_be_bytes ats).val) ∧
        out = self.prev.data.val.slice (off + 4) (off + 36) ∧
        (∀ j, j < off → self'.prev.data[j]! = self.prev.data[j]!) ∧
        (off + 36 < self.prev.data.length →
          self'.prev.data = (self.prev.data.val.setSlice! off
            (self.prev.data.val.drop (self.prev.data.length - 36))).take
              (self.prev.data.length - 36)) ∧
        (off + 36 = self.prev.data.length →
          self'.prev.data = self.prev.data.val.take off))

/-- Postcondition for the greater+within-jump case of `ChainEpochDirection.key`:
chain advancement from `self.ctr` to `ats`. -/
def cedKeyAdvancePost (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (result : core.result.Result (alloc.vec.Vec U8) Error)
    (self' : chain.ChainEpochDirection)
    (h_gt : ats > self.ctr) : Prop :=
  let loopSteps := ats.val - (self.ctr.val + 1)
  let loopSecret := chain.ChainEpochDirection.iterChainSecret self.next.val self.ctr.val loopSteps
  let ctrAts : U32 := ⟨ats.val, by scalar_tac⟩
  let finalOkm := nextKeyHkdfOutput loopSecret ctrAts
  let kh0 :=
    if ats.val > self.ctr.val + (chain.maxOoo params).val
    then { data := ⟨[], by simp⟩ : chain.KeyHistory }
    else self.prev
  let khPreGc := chain.ChainEpochDirection.iterKeyHistory
    self.next.val self.ctr.val ats.val params kh0 loopSteps
  let max_ooo : Nat := (chain.maxOoo params).val
  let trim_threshold : Nat := (max_ooo * 11 / 10 + 1) * 36
  let ctr_new : U32 := ⟨ats.val - 1, by scalar_tac⟩
  (∃ key : alloc.vec.Vec U8,
    result = core.result.Result.Ok key ∧
    key.length = 32 ∧
    key.val = finalOkm.drop 32) ∧
  self'.ctr = ats.val ∧
  self'.next.length = 32 ∧
  self'.next.val = finalOkm.take 32 ∧
  self'.prev.data.length % 36 = 0 ∧
  self'.prev.data.length ≤
    kh0.data.length + 36 * (ats.val - self.ctr.val) ∧
  self'.prev.data.length ≤ self.prev.data.length + 36 * (ats.val - self.ctr.val) ∧
  (ats.val > self.ctr.val + (chain.maxOoo params).val →
    self'.prev.data.length ≤ 36 * (ats.val - self.ctr.val)) ∧
  self'.prev.data.length ≤ Usize.max ∧
  self'.prev.data.length ≤ khPreGc.data.length ∧
  khPreGc.data.length % 36 = 0 ∧
  kh0.data.length ≤ khPreGc.data.length ∧
  keyPostGc self' khPreGc max_ooo trim_threshold ctr_new

/-- Full postcondition for `ChainEpochDirection.key`, covering all four cases. -/
def cedKeyPost (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (result : core.result.Result (alloc.vec.Vec U8) Error)
    (self' : chain.ChainEpochDirection) : Prop :=
  (ats = self.ctr →
    result = core.result.Result.Err (Error.KeyAlreadyRequested ats) ∧
    self' = self) ∧
  (ats < self.ctr →
    cedKeyLessPost self ats params result self') ∧
  (ats > self.ctr →
    ats.val - self.ctr.val > (chain.maxJump params).val →
    result = core.result.Result.Err (Error.KeyJump self.ctr ats) ∧
    self' = self) ∧
  (∀ (h_gt : ats > self.ctr),
    ats.val - self.ctr.val ≤ (chain.maxJump params).val →
    cedKeyAdvancePost self ats params result self' h_gt)
/-- Per-entry postcondition for `recv_key`: relates old `ce`, new `ce'`,
and result across all four cases.  Delegates directly to `cedKeyPost` on the
`recv` direction, which avoids a vacuous existential in the advance case. -/
def recvKeyEpochPost (self : chain.Chain) (index : U32)
    (ce ce' : chain.ChainEpoch)
    (result : core.result.Result (alloc.vec.Vec U8) Error) : Prop :=
  ce'.send = ce.send ∧
  cedKeyPost ce.recv index self.params result ce'.recv

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



/-- Bridge: convert destructured `GcPost` components (after
`unfold GcPost` + `rw [maxOoo_if_eq]`) into `keyPostGc`.

The hypothesis `gc_trim` keeps the `ValidRecord`/`IsExpired`/`RecordsEq`
abbreviations from `GcPost`; the proof unfolds `keyPostGc` and repackages. -/
theorem keyPostGc_of_GcPost
    (ced' : chain.ChainEpochDirection)
    (khPreGc : chain.KeyHistory)
    (current_key ctr_new : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_ctr_eq : current_key.val = ctr_new.val)
    (gc_shrink : ced'.prev.data.length ≤ khPreGc.data.length)
    (gc_noop : khPreGc.data.length <
        ((chain.maxOoo params).val * 11 / 10 + 1) * 36 →
      ced'.prev = khPreGc)
    (gc_trim : ((chain.maxOoo params).val * 11 / 10 + 1) * 36 ≤
        khPreGc.data.length →
      ∃ horizon : U32,
        horizon.val = current_key.val - (chain.maxOoo params).val ∧
        (∀ m, chain.KeyHistory.ValidRecord ced'.prev.data m →
          ¬chain.KeyHistory.IsExpired
            (chain.KeyHistory.horizonSlice horizon) ced'.prev.data m) ∧
        (∀ n, chain.KeyHistory.ValidRecord khPreGc.data n →
          ¬chain.KeyHistory.IsExpired
            (chain.KeyHistory.horizonSlice horizon) khPreGc.data n →
          ∃ m, chain.KeyHistory.ValidRecord ced'.prev.data m ∧
            chain.KeyHistory.RecordsEq ced'.prev.data m khPreGc.data n) ∧
        (∃ f₀ : Nat → Nat,
          (∀ m, chain.KeyHistory.ValidRecord ced'.prev.data m →
            chain.KeyHistory.ValidRecord khPreGc.data (f₀ m) ∧
            chain.KeyHistory.RecordsEq ced'.prev.data m
              khPreGc.data (f₀ m)) ∧
          (∀ m₁ m₂,
            chain.KeyHistory.ValidRecord ced'.prev.data m₁ →
            chain.KeyHistory.ValidRecord ced'.prev.data m₂ →
            f₀ m₁ = f₀ m₂ → m₁ = m₂)) ∧
        (∃ g₀ : Nat → Nat,
          (∀ n, chain.KeyHistory.ValidRecord khPreGc.data n →
            ¬chain.KeyHistory.IsExpired
              (chain.KeyHistory.horizonSlice horizon) khPreGc.data n →
            chain.KeyHistory.ValidRecord ced'.prev.data (g₀ n) ∧
            chain.KeyHistory.RecordsEq ced'.prev.data (g₀ n)
              khPreGc.data n) ∧
          (∀ n₁ n₂,
            chain.KeyHistory.ValidRecord khPreGc.data n₁ →
            chain.KeyHistory.ValidRecord khPreGc.data n₂ →
            ¬chain.KeyHistory.IsExpired
              (chain.KeyHistory.horizonSlice horizon) khPreGc.data n₁ →
            ¬chain.KeyHistory.IsExpired
              (chain.KeyHistory.horizonSlice horizon) khPreGc.data n₂ →
            g₀ n₁ = g₀ n₂ → n₁ = n₂))) :
    keyPostGc ced' khPreGc
      (chain.maxOoo params).val
      (((chain.maxOoo params).val * 11 / 10 + 1) * 36)
      ctr_new := by
  unfold keyPostGc
  refine ⟨?_, ?_, gc_noop, ?_, ?_⟩
  · intro htrim hmo
    obtain ⟨hz, hhz, hlive, _, _, _⟩ := gc_trim (le_trans htrim gc_shrink)
    exact ⟨hz, by rw [hhz, h_ctr_eq], fun m hm => hlive m hm⟩
  · intro htrim hmo
    obtain ⟨hz, hhz, _, hcomp, _, _⟩ := gc_trim htrim
    refine ⟨hz, by rw [hhz, h_ctr_eq], fun n hn hne => ?_⟩
    obtain ⟨m, ⟨hml, hmmod⟩, hmeq⟩ := hcomp n hn hne
    exact ⟨m, hml, hmmod, hmeq⟩
  · intro htrim hmo
    obtain ⟨_, _, _, _, ⟨f, hfp, hfi⟩, _⟩ := gc_trim htrim
    exact ⟨f,
      fun m hm => let ⟨hv, hr⟩ := hfp m hm; ⟨hv.1, hv.2, hr⟩,
      fun m₁ m₂ h1 h2 => hfi m₁ m₂ h1 h2⟩
  · intro htrim hmo
    obtain ⟨hz, hhz, _, _, _, ⟨gf, hgp, hgi⟩⟩ := gc_trim htrim
    refine ⟨hz, by rw [hhz, h_ctr_eq], gf,
      fun n hn hne =>
        let ⟨hv, hr⟩ := hgp n hn hne; ⟨hv.1, hv.2, hr⟩,
      fun n₁ n₂ h1 h2 e1 e2 => hgi n₁ n₂ h1 h2 e1 e2⟩

end spqr.chain
