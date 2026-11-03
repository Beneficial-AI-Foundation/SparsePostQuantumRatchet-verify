/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.V1.Unchunked.SendEk.Serialize.HeaderSent.FunctionalModels
public import Spqr.Specs.V1.Unchunked.SendEk.Serialize.EkSent.FunctionalModels
/-!
# Spec theorem for `spqr::v1::unchunked::send_ek::{HeaderSent}::send_ek`

`HeaderSent::send_ek` is the second step of the encapsulation-key-sending (A→B) side of the
unchunked V1 ratchet.  Holding `HeaderSent {epoch, auth, ek, dk}` after `send_header`, A
returns the 1152-byte `ek` to the caller for transmission and moves to `EkSent {epoch, auth, dk}`,
dropping `ek`.

No cryptography happens here: `ek` is already bound to the epoch via the authenticated header
hash `H(ek)`.  The function is a pure record construction that never fails.

The hax contract is `ensures(|(_, ek)| ek.len() == 1152)` with no `requires`; since the returned
`ek` is `self.ek`, this follows from the `HeaderSent` refinement
(`HeaderSent.FunctionalModels.WellFormed`), and the `dk.len() == 2400` refinement is preserved
into `EkSent` (see `EkSent.FunctionalModels.WellFormed`).

**Source**: spqr/src/v1/unchunked/send_ek.rs (lines 106:4-115:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace Spqr.V1.Unchunked.SendEk.HeaderSent

open spqr.v1.unchunked.send_ek

/-- Successor state of `HeaderSent::send_ek`: `epoch`, `auth`, `dk` carried over, `ek` dropped. -/
def sendEkState (self : HeaderSent) : EkSent :=
  { epoch := self.epoch, auth := self.auth, dk := self.dk }

/-- Full result of `HeaderSent::send_ek`: the successor state paired with `self.ek`. -/
def sendEkResult (self : HeaderSent) : EkSent × alloc.vec.Vec U8 :=
  (sendEkState self, self.ek)

end Spqr.V1.Unchunked.SendEk.HeaderSent

namespace spqr.v1.unchunked.send_ek.HeaderSent

open Spqr.V1.Unchunked.SendEk.HeaderSent

/-- **Exact characterisation of `spqr.v1.unchunked.send_ek.HeaderSent.send_ek`**:

With no precondition and no fallible operation, `send_ek self = ok (sendEkResult self)`;
in particular it never returns `fail _` or `div`. -/
theorem send_ek_eq (self : HeaderSent) :
    send_ek self = ok (sendEkResult self) := by
  rfl

/-- **Spec theorem for `spqr.v1.unchunked.send_ek.HeaderSent.send_ek`**:

• Takes `self = {epoch, auth, ek, dk}`; requires nothing and never panics.
• Returns `ok ({ epoch := self.epoch, auth := self.auth, dk := self.dk }, self.ek)`,
  i.e. `result = sendEkResult self`. -/
@[step]
theorem send_ek_spec (self : HeaderSent) :
    send_ek self ⦃ (result : EkSent × alloc.vec.Vec U8) =>
      result = sendEkResult self ⦄ := by
  unfold send_ek
  step*
  rfl

/-- **Spec theorem for `spqr.v1.unchunked.send_ek.HeaderSent.send_ek`** (field-wise form):

`send_ek_spec` with the result spelled out field by field. -/
theorem send_ek_spec_fields (self : HeaderSent) :
    send_ek self ⦃ (result : EkSent × alloc.vec.Vec U8) =>
      let state := result.1
      let ek := result.2
      state.epoch = self.epoch ∧ state.auth = self.auth ∧
      state.dk = self.dk ∧ ek = self.ek ⦄ := by
  apply WP.spec_mono (send_ek_spec self)
  intro result h
  subst h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Spec theorem for `spqr.v1.unchunked.send_ek.HeaderSent.send_ek`** (hax `ensures` and
well-formedness preservation):

Under the input invariant `HeaderSent.FunctionalModels.WellFormed self`
(`ek.length = 1152 ∧ dk.length = 2400`), the returned `ek` satisfies the hax postcondition
`ek.len() == 1152` and the successor state is `EkSent.FunctionalModels.WellFormed`.
Projection of `send_ek_spec`. -/
theorem send_ek_spec_wellFormed (self : HeaderSent)
    (h_wf : serialize.HeaderSent.FunctionalModels.WellFormed self) :
    send_ek self ⦃ (result : EkSent × alloc.vec.Vec U8) =>
      let state := result.1
      let ek := result.2
      ek.length = 1152 ∧
      serialize.EkSent.FunctionalModels.WellFormed state ⦄ := by
  apply WP.spec_mono (send_ek_spec self)
  intro result h
  subst h
  exact h_wf

end spqr.v1.unchunked.send_ek.HeaderSent
