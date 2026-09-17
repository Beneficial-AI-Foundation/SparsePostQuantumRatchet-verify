/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Chain.Chain.SendKey
/-! # 64-bit specialization of `send_key_spec`

On 64-bit platforms (`System.Platform.numBits = 64`) the `h_diff_fits` precondition of
`send_key_spec` is trivially satisfied: `epoch` and `current_epoch` are both `U64`, so their
difference is at most `U64.max = Usize.max` on a 64-bit target.  Since `h_diff_fits` only
requires `≤ Usize.max`, it holds automatically.

This file provides `send_key_spec_64`, which drops `h_diff_fits` entirely and assumes
`System.Platform.numBits = 64` instead. -/

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr.chain.Chain

/-- **64-bit specialization of `send_key_spec`**.

Identical postcondition to `send_key_spec` but with `h_diff_fits` dropped.
The hypothesis `System.Platform.numBits = 64` makes `Usize.max = U64.max`,
so `current_epoch - epoch ≤ U64.max = Usize.max` holds for all `U64` values.

See `send_key_spec` for full documentation of the postcondition. -/
theorem send_key_spec_64 (self : chain.Chain) (epoch : U64)
    (h_64 : System.Platform.numBits = 64)
    (h_wf : self.links.head.val + self.links.length.val ≤ self.links.buf.val.length)
    (h_target : self.send_epoch.val ≤ epoch.val → epoch.val ≤ self.current_epoch.val →
      self.current_epoch.val - epoch.val < self.links.length.val →
      match self.links.buf.val[self.links.head.val + sendKeyIdx self epoch]? with
      | none => True
      | some ce => ce.send.next.length = 32 ∧ ce.send.ctr < U32.max) :
    send_key self epoch ⦃ (result : (core.result.Result (U32 × alloc.vec.Vec U8) Error) ×
        chain.Chain) =>
      match result.1 with
      | core.result.Result.Err e =>
          result.2 = self ∧
          ((e = Error.SendKeyEpochDecreased self.send_epoch epoch ∧
              epoch.val < self.send_epoch.val) ∨
           (e = Error.EpochOutOfRange epoch ∧ self.send_epoch.val ≤ epoch.val ∧
              (epoch.val > self.current_epoch.val ∨
               self.current_epoch.val - epoch.val ≥ self.links.length.val)))
      | core.result.Result.Ok (i, key) =>
          let idx := sendKeyIdx self epoch
          let ei := sendKeyEi self epoch
          let phys := self.links.head.val + idx
          self.send_epoch.val ≤ epoch.val ∧
          epoch.val ≤ self.current_epoch.val ∧
          self.current_epoch.val - epoch.val < self.links.length.val ∧
          match self.links.buf.val[phys]? with
          | none => False
          | some ce =>
            i.val = ce.send.ctr.val + 1 ∧
            key.length = 32 ∧
            key.val = (nextKeyHkdfOutput ce.send.next i).drop 32 ∧
            result.2.dir = self.dir ∧
            result.2.current_epoch = self.current_epoch ∧
            result.2.send_epoch = epoch ∧
            result.2.next_root = self.next_root ∧
            result.2.params = self.params ∧
            result.2.links.head.val = self.links.head.val + (idx - ei) ∧
            result.2.links.length.val = self.links.length.val - (idx - ei) ∧
            result.2.links.buf.val.length = self.links.buf.val.length ∧
            result.2.links.head.val + result.2.links.length.val ≤ result.2.links.buf.val.length ∧
            ei < result.2.links.length.val ∧
            (match result.2.links.buf.val[phys]? with
             | none => False
             | some ce' =>
                 ce'.recv = ce.recv ∧
                 ce'.send.ctr = i ∧
                 ce'.send.next.length = ce.send.next.length ∧
                 ce'.send.next.val = (nextKeyHkdfOutput ce.send.next i).take 32 ∧
                 ce'.send.prev = ce.send.prev) ∧
            (self.send_epoch = epoch →
              result.2.links.head = self.links.head ∧
              result.2.links.length = self.links.length ∧
              ∀ j, j ≠ phys →
                result.2.links.buf.val[j]? = self.links.buf.val[j]?) ∧
            (self.send_epoch ≠ epoch →
              ∀ j, self.links.head.val + (idx - ei) ≤ j → j < phys →
                clearedAt self.links result.2.links j) ∧
            (∀ j, (j < self.links.head.val + (idx - ei) ∨ phys < j) →
              result.2.links.buf.val[j]? = self.links.buf.val[j]?) ⦄ := by
  apply send_key_spec self epoch _ h_wf h_target
  intro h_le h_le'
  have h_usize : Usize.max ≥ 2 ^ 64 - 1 := by
    have := Usize.max_succ_eq_pow; rw [h_64] at this; omega
  have h_ce : self.current_epoch.val < 2 ^ 64 := by scalar_tac
  omega

end spqr.chain.Chain
