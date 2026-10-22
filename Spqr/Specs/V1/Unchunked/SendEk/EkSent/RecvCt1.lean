/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.V1.Unchunked.SendEk.Serialize.EkSent.FunctionalModels
public import Spqr.Specs.V1.Unchunked.SendEk.Serialize.EkSentCt1Received.FunctionalModels
/-!
# Spec theorem for `spqr::v1::unchunked::send_ek::{EkSent}::recv_ct1`

`EkSent::recv_ct1` is the step on the key-sending (A→B) side of the unchunked V1 ratchet in
which A, having already published the header and the full 1152-byte ML-KEM-768 encapsulation
key `ek`, receives from B the 960-byte first ciphertext half `ct1` of the incremental
encapsulation against that key.  Consuming the `EkSent` state `{epoch, auth, dk}` the function:

  1. asserts `epoch == self.epoch`, i.e. that the peer is answering for the epoch whose
     encapsulation key A actually sent;
  2. returns the successor state `EkSentCt1Received {epoch, auth, dk, ct1}`, carrying
     `epoch`, `auth` and the 2400-byte compressed decapsulation key `dk` over unchanged and
     retaining the received `ct1` so that it can later be combined with `ct2` in `recv_ct2`.

No cryptography happens here: `ct1` cannot be authenticated on its own, since the tag received
with `ct2` covers the *complete* ciphertext `c₁ ‖ c₂`.  The function merely stores `ct1`; the
check is deferred to `EkSentCt1Received::recv_ct2`.

The hax contract on the Rust function is `requires(epoch == self.epoch && ct1.len() == 960)`.
Only the first conjunct is needed for totality (it discharges the `assert_eq!`); the second
conjunct is the `#[hax_lib::refine(ct1.len() == 960)]` invariant of the `EkSentCt1Received`
struct (see `EkSentCt1Received.FunctionalModels.WellFormed`) and is only needed to show that
the successor state is well formed.  The spec below therefore assumes only `epoch = self.epoch`
for the main theorem and pins the result down exactly; well-formedness preservation and the
exact panic condition are stated separately.

**Source**: spqr/src/v1/unchunked/send_ek.rs (lines 121:4-133:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

/- Helper definitions live in a CamelCase namespace (mirroring `Spqr.V1.Unchunked.SendCt` in
`SendCt1.lean`) so that their full names satisfy the `defsWithUnderscore` linter; the spec
theorems themselves stay in the Rust-mirroring `spqr.v1.unchunked.send_ek.EkSent` namespace. -/
namespace Spqr.V1.Unchunked.SendEk.EkSent

open spqr.v1.unchunked.send_ek

/-- The successor state produced by `EkSent::recv_ct1`: every field of `self` is carried over
unchanged and the received first ciphertext half `ct1` is stored alongside. -/
def recvCt1Result (self : EkSent) (ct1 : alloc.vec.Vec U8) : EkSentCt1Received :=
  { epoch := self.epoch, auth := self.auth, dk := self.dk, ct1 }

end Spqr.V1.Unchunked.SendEk.EkSent

namespace spqr.v1.unchunked.send_ek.EkSent

open Spqr.V1.Unchunked.SendEk.EkSent

/-- **Spec theorem for `spqr.v1.unchunked.send_ek.EkSent.recv_ct1`**:

• Takes the `EkSent` state `self = {epoch, auth, dk}`, the epoch `epoch` announced by the peer
  and the received first ciphertext half `ct1`.
• Checks `massert (epoch = self.epoch)`, which succeeds because of `h_epoch`.
• Returns `ok { epoch := self.epoch, auth := self.auth, dk := self.dk, ct1 }`.

• Requires only the first conjunct of the hax precondition:
    `h_epoch : epoch = self.epoch`
  Under this hypothesis the call always succeeds (no panic) and the result is fully
  determined: the function is a pure record construction.

The result satisfies the postcondition

  `result = recvCt1Result self ct1`

i.e. `result.epoch = self.epoch`, `result.auth = self.auth`, `result.dk = self.dk` and
`result.ct1 = ct1`.

The proof unfolds `recv_ct1` and lets `step*` discharge the assertion (from `h_epoch`); the
remaining goal is closed by reflexivity.

**Source**: spqr/src/v1/unchunked/send_ek.rs (lines 121:4-133:5)
-/
@[step]
theorem recv_ct1_spec (self : EkSent) (epoch : U64) (ct1 : alloc.vec.Vec U8)
    (h_epoch : epoch = self.epoch) :
    recv_ct1 self epoch ct1 ⦃ (result : EkSentCt1Received) =>
      result = recvCt1Result self ct1 ⦄ := by
  unfold recv_ct1
  step*
  rfl

/-- **Spec theorem for `spqr.v1.unchunked.send_ek.EkSent.recv_ct1`** (field-wise form):

The same statement as `recv_ct1_spec`, but with the successor state spelled out field by
field.  Projection of `recv_ct1_spec`.

**Source**: spqr/src/v1/unchunked/send_ek.rs (lines 121:4-133:5)
-/
theorem recv_ct1_spec_fields (self : EkSent) (epoch : U64) (ct1 : alloc.vec.Vec U8)
    (h_epoch : epoch = self.epoch) :
    recv_ct1 self epoch ct1 ⦃ (result : EkSentCt1Received) =>
      result.epoch = self.epoch ∧ result.auth = self.auth ∧
      result.dk = self.dk ∧ result.ct1 = ct1 ⦄ := by
  apply WP.spec_mono (recv_ct1_spec self epoch ct1 h_epoch)
  intro result h
  subst h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Spec theorem for `spqr.v1.unchunked.send_ek.EkSent.recv_ct1`** (well-formedness
preservation):

Under the full hax precondition — `epoch = self.epoch` and `ct1.length = 960` — and the
`#[hax_lib::refine(dk.len() == 2400)]` invariant of the input state, the successor state
satisfies the `#[hax_lib::refine]` invariants of `EkSentCt1Received`, i.e.
`dk.length = 2400 ∧ ct1.length = 960`.  Projection of `recv_ct1_spec`.

**Source**: spqr/src/v1/unchunked/send_ek.rs (lines 121:4-133:5)
-/
theorem recv_ct1_spec_wellFormed (self : EkSent) (epoch : U64) (ct1 : alloc.vec.Vec U8)
    (h_epoch : epoch = self.epoch)
    (h_wf : serialize.EkSent.FunctionalModels.WellFormed self)
    (h_ct1 : ct1.length = 960) :
    recv_ct1 self epoch ct1 ⦃ (result : EkSentCt1Received) =>
      serialize.EkSentCt1Received.FunctionalModels.WellFormed result ⦄ := by
  apply WP.spec_mono (recv_ct1_spec self epoch ct1 h_epoch)
  intro result h
  subst h
  exact ⟨h_wf, h_ct1⟩

/-- **Completeness of the precondition of `spqr.v1.unchunked.send_ek.EkSent.recv_ct1`**:

The hypothesis `epoch = self.epoch` of `recv_ct1_spec` is not merely sufficient but necessary:
whenever the announced epoch differs from the stored one, the `assert_eq!` fires and the call
panics.  Together with `recv_ct1_spec` this characterises the function exactly:

  `recv_ct1 self epoch ct1 = if epoch = self.epoch then ok (recvCt1Result self ct1)
                              else fail assertionFailure`

**Source**: spqr/src/v1/unchunked/send_ek.rs (lines 121:4-133:5)
-/
theorem recv_ct1_fail_of_epoch_ne (self : EkSent) (epoch : U64) (ct1 : alloc.vec.Vec U8)
    (h_epoch : epoch ≠ self.epoch) :
    recv_ct1 self epoch ct1 = fail Error.assertionFailure := by
  simp [recv_ct1, massert, h_epoch]

end spqr.v1.unchunked.send_ek.EkSent
