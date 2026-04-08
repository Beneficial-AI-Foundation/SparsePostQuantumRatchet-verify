/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Continuous Key Agreement (CKA)

Definition 12 from Alwen-Coretti-Dodis "The Double Ratchet: Security Notions,
Proofs, and Modularization for the Signal Protocol" (2020).

CKA is a synchronous two-party protocol. Odd rounds i consist of A sending
and B receiving a message Tᵢ; in even rounds B is the sender and A the receiver.
Each round also produces a key Iᵢ, output by the sender upon sending Tᵢ and
by the receiver upon receiving Tᵢ.

## Design: Two-state formulation

The sender/receiver state types swap after each operation, matching the
alternating-epoch structure. After A sends, her state becomes `ReceiverState`
(she will next receive). After B receives, his state becomes `SenderState`
(he will next send).
-/

set_option autoImplicit false

open OracleComp

namespace CKA

/-- A continuous-key-agreement (CKA) scheme is a quadruple of algorithms
`(Init, Send, Recv)` operating over shared keys, states, messages, and output keys.

- `init` takes a shared key and produces the initial sender and receiver states
- `send` takes a sender state and produces a new (receiver) state, a message, and a key
- `recv` takes a receiver state and a message, producing a new (sender) state and a key

The state types swap after each operation: after sending, the party holds a
`ReceiverState`; after receiving, a `SenderState`. -/
structure CKAScheme (SharedKey SenderState ReceiverState Msg Output : Type) where
  /-- Initialize both parties from a shared key. -/
  init : SharedKey → ProbComp (SenderState × ReceiverState)
  /-- Sender produces a new state, public message, and agreed key. -/
  send : SenderState → ProbComp (ReceiverState × Msg × Output)
  /-- Receiver processes a message, producing a new state and agreed key. -/
  recv : ReceiverState → Msg → ProbComp (SenderState × Output)

/-- A CKA scheme with explicit sender randomness, needed for the `send-P'(r)` oracle
in Figure 3 where the adversary can choose the sending randomness.

- `sendDet` is the deterministic core of `send`: given a sender state and coins,
  it produces the new receiver state, message, and output key without sampling.
- The randomized `send` is derived via `toCKAScheme` by sampling coins uniformly.
- `recv` remains unchanged (deterministic in all known CKA constructions). -/
structure CKASchemeWithCoins
    (SharedKey SenderState ReceiverState Msg Output SendCoins : Type) where
  /-- Initialize both parties from a shared key. -/
  init : SharedKey → ProbComp (SenderState × ReceiverState)
  /-- Deterministic send: given sender state and explicit coins, produce
  new receiver state, message, and output key. -/
  sendDet : SenderState → SendCoins → (ReceiverState × Msg × Output)
  /-- Receiver processes a message, producing a new state and agreed key. -/
  recv : ReceiverState → Msg → ProbComp (SenderState × Output)

/-- Derive a `CKAScheme` from a `CKASchemeWithCoins` by sampling coins uniformly. -/
noncomputable def CKASchemeWithCoins.toCKAScheme
    {SharedKey SenderState ReceiverState Msg Output SendCoins : Type}
    [SampleableType SendCoins]
    (cka : CKASchemeWithCoins SharedKey SenderState ReceiverState Msg Output SendCoins) :
    CKAScheme SharedKey SenderState ReceiverState Msg Output where
  init := cka.init
  send ss := do let r ← $ᵗ SendCoins; pure (cka.sendDet ss r)
  recv := cka.recv

end CKA
