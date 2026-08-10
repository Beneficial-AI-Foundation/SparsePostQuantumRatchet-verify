/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Spqr.Specs.External

/-! # States.send Specifications

Specifications and proofs for branches of `States.send`
(PROP-33 from `docs/mlkembraid_spec/3_protocol.md` and PROP-21 from `docs/mlkembraid_spec/1_scka_interface.md`).

**PROP-33:** In the `EkSentCt1Received` state, `send` emits `Ct1Ack(true)`.

**PROP-21:** For 10 of 11 state variants, `send` emits `key = none`.
The exception is `HeaderReceived`, which emits `key = some epoch_secret`.
Three variants (EkSentCt1Received, NoHeaderReceived, Ct1Acknowledged) need
no axioms; the other 7 rely on liveness axioms for `next_chunk` (encoding)
and `send_hdr_chunk`/`send_ct1_chunk` (crypto+RNG) from `External.lean`.

**Source**: spqr/src/v1/chunked/states.rs (lines 139-268)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/-! ## PROP-33: Main theorem -/

/-- **PROP-33 — EkSentCt1Received.send emits Ct1Ack(true).**

When the state machine is in `EkSentCt1Received`, `States.send` returns
`Ok` with `msg.payload = Ct1Ack true`, `key = none`, and state unchanged.
This is a deviation flag: the spec's `Ct1Ack` carries no boolean, but the
implementation always sends `true` here. -/
@[step]
theorem v1.chunked.states.States.send_EkSentCt1Received_ct1_ack
    {R : Type} (rng_inst : rand.rng.Rng R) (crypto_inst : rand_core.CryptoRng R)
    (state : v1.chunked.send_ek.EkSentCt1Received) (rng : R) :
    v1.chunked.states.States.send rng_inst crypto_inst
      (v1.chunked.states.States.EkSentCt1Received state) rng ⦃ r =>
      ∃ s, r.1 = core.result.Result.Ok s ∧
      s.msg.payload = v1.chunked.states.MessagePayload.Ct1Ack true ∧
      s.key = none ∧
      s.state = v1.chunked.states.States.EkSentCt1Received state ∧
      r.2 = rng ⦄ := by
  unfold v1.chunked.states.States.send v1.chunked.send_ek.EkSentCt1Received.epoch
  step*

/-! ## PROP-21 (partial): NoHeaderReceived.send and Ct1Acknowledged.send -/

/-- **PROP-21 partial (NoHeaderReceived)** — `send` emits `payload = None`,
`key = none`, state unchanged, RNG not consumed. -/
@[step]
theorem v1.chunked.states.States.send_NoHeaderReceived_noop
    {R : Type} (rng_inst : rand.rng.Rng R) (crypto_inst : rand_core.CryptoRng R)
    (state : v1.chunked.send_ct.NoHeaderReceived) (rng : R) :
    v1.chunked.states.States.send rng_inst crypto_inst
      (v1.chunked.states.States.NoHeaderReceived state) rng ⦃ r =>
      ∃ s, r.1 = core.result.Result.Ok s ∧
      s.msg.payload = v1.chunked.states.MessagePayload.None ∧
      s.key = none ∧
      s.state = v1.chunked.states.States.NoHeaderReceived state ∧
      r.2 = rng ⦄ := by
  unfold v1.chunked.states.States.send v1.chunked.send_ct.NoHeaderReceived.epoch
  step*

/-- **PROP-21 partial (Ct1Acknowledged)** — `send` emits `payload = None`,
`key = none`, state unchanged, RNG not consumed. -/
@[step]
theorem v1.chunked.states.States.send_Ct1Acknowledged_noop
    {R : Type} (rng_inst : rand.rng.Rng R) (crypto_inst : rand_core.CryptoRng R)
    (state : v1.chunked.send_ct.Ct1Acknowledged) (rng : R) :
    v1.chunked.states.States.send rng_inst crypto_inst
      (v1.chunked.states.States.Ct1Acknowledged state) rng ⦃ r =>
      ∃ s, r.1 = core.result.Result.Ok s ∧
      s.msg.payload = v1.chunked.states.MessagePayload.None ∧
      s.key = none ∧
      s.state = v1.chunked.states.States.Ct1Acknowledged state ∧
      r.2 = rng ⦄ := by
  unfold v1.chunked.states.States.send v1.chunked.send_ct.Ct1Acknowledged.epoch
  step*

/-! ## PROP-21: Remaining key=none variants (axiom-backed)

The following 7 variants call helper functions before returning `key := none`.
The proofs unfold `States.send`, the variant's `.epoch`, and (for simple helpers)
the helper itself to expose the `next_chunk` call. For the complex
`KeysUnsampled.send_hdr_chunk`, the axiom is at the helper level.
-/

/-- **PROP-21 (KeysUnsampled)** — `send` emits `key = none`.
Uses liveness axiom for `send_hdr_chunk` (complex: RNG + MLKEM). -/
@[step]
theorem v1.chunked.states.States.send_KeysUnsampled_key_none
    {R : Type} (rng_inst : rand.rng.Rng R) (crypto_inst : rand_core.CryptoRng R)
    (state : v1.chunked.send_ek.KeysUnsampled) (rng : R) :
    v1.chunked.states.States.send rng_inst crypto_inst
      (v1.chunked.states.States.KeysUnsampled state) rng ⦃ r =>
      ∃ s, r.1 = core.result.Result.Ok s ∧ s.key = none ⦄ := by
  unfold v1.chunked.states.States.send v1.chunked.send_ek.KeysUnsampled.epoch
  step*

/-- **PROP-21 (KeysSampled)** — `send` emits `key = none`.
Uses liveness axiom for `next_chunk`. -/
@[step]
theorem v1.chunked.states.States.send_KeysSampled_key_none
    {R : Type} (rng_inst : rand.rng.Rng R) (crypto_inst : rand_core.CryptoRng R)
    (state : v1.chunked.send_ek.KeysSampled) (rng : R) :
    v1.chunked.states.States.send rng_inst crypto_inst
      (v1.chunked.states.States.KeysSampled state) rng ⦃ r =>
      ∃ s, r.1 = core.result.Result.Ok s ∧ s.key = none ⦄ := by
  unfold v1.chunked.states.States.send v1.chunked.send_ek.KeysSampled.epoch
    v1.chunked.send_ek.KeysSampled.send_hdr_chunk
  step*

/-- **PROP-21 (HeaderSent)** — `send` emits `key = none`.
Uses liveness axiom for `next_chunk`. -/
@[step]
theorem v1.chunked.states.States.send_HeaderSent_key_none
    {R : Type} (rng_inst : rand.rng.Rng R) (crypto_inst : rand_core.CryptoRng R)
    (state : v1.chunked.send_ek.HeaderSent) (rng : R) :
    v1.chunked.states.States.send rng_inst crypto_inst
      (v1.chunked.states.States.HeaderSent state) rng ⦃ r =>
      ∃ s, r.1 = core.result.Result.Ok s ∧ s.key = none ⦄ := by
  unfold v1.chunked.states.States.send v1.chunked.send_ek.HeaderSent.epoch
    v1.chunked.send_ek.HeaderSent.send_ek_chunk
  step*

/-- **PROP-21 (Ct1Received)** — `send` emits `key = none`.
Uses liveness axiom for `next_chunk`. -/
@[step]
theorem v1.chunked.states.States.send_Ct1Received_key_none
    {R : Type} (rng_inst : rand.rng.Rng R) (crypto_inst : rand_core.CryptoRng R)
    (state : v1.chunked.send_ek.Ct1Received) (rng : R) :
    v1.chunked.states.States.send rng_inst crypto_inst
      (v1.chunked.states.States.Ct1Received state) rng ⦃ r =>
      ∃ s, r.1 = core.result.Result.Ok s ∧ s.key = none ⦄ := by
  unfold v1.chunked.states.States.send v1.chunked.send_ek.Ct1Received.epoch
    v1.chunked.send_ek.Ct1Received.send_ek_chunk
  step*

/-- **PROP-21 (Ct1Sampled)** — `send` emits `key = none`.
Uses liveness axiom for `next_chunk`. -/
@[step]
theorem v1.chunked.states.States.send_Ct1Sampled_key_none
    {R : Type} (rng_inst : rand.rng.Rng R) (crypto_inst : rand_core.CryptoRng R)
    (state : v1.chunked.send_ct.Ct1Sampled) (rng : R) :
    v1.chunked.states.States.send rng_inst crypto_inst
      (v1.chunked.states.States.Ct1Sampled state) rng ⦃ r =>
      ∃ s, r.1 = core.result.Result.Ok s ∧ s.key = none ⦄ := by
  unfold v1.chunked.states.States.send v1.chunked.send_ct.Ct1Sampled.epoch
    v1.chunked.send_ct.Ct1Sampled.send_ct1_chunk
  step*

/-- **PROP-21 (EkReceivedCt1Sampled)** — `send` emits `key = none`.
Uses liveness axiom for `next_chunk`. -/
@[step]
theorem v1.chunked.states.States.send_EkReceivedCt1Sampled_key_none
    {R : Type} (rng_inst : rand.rng.Rng R) (crypto_inst : rand_core.CryptoRng R)
    (state : v1.chunked.send_ct.EkReceivedCt1Sampled) (rng : R) :
    v1.chunked.states.States.send rng_inst crypto_inst
      (v1.chunked.states.States.EkReceivedCt1Sampled state) rng ⦃ r =>
      ∃ s, r.1 = core.result.Result.Ok s ∧ s.key = none ⦄ := by
  unfold v1.chunked.states.States.send v1.chunked.send_ct.EkReceivedCt1Sampled.epoch
    v1.chunked.send_ct.EkReceivedCt1Sampled.send_ct1_chunk
  step*

/-- **PROP-21 (Ct2Sampled)** — `send` emits `key = none`.
Uses liveness axiom for `next_chunk`. -/
@[step]
theorem v1.chunked.states.States.send_Ct2Sampled_key_none
    {R : Type} (rng_inst : rand.rng.Rng R) (crypto_inst : rand_core.CryptoRng R)
    (state : v1.chunked.send_ct.Ct2Sampled) (rng : R) :
    v1.chunked.states.States.send rng_inst crypto_inst
      (v1.chunked.states.States.Ct2Sampled state) rng ⦃ r =>
      ∃ s, r.1 = core.result.Result.Ok s ∧ s.key = none ⦄ := by
  unfold v1.chunked.states.States.send v1.chunked.send_ct.Ct2Sampled.epoch
    v1.chunked.send_ct.Ct2Sampled.send_ct2_chunk
  step*

/-! ## PROP-21 positive case: HeaderReceived emits a key -/

/-- **PROP-21 (HeaderReceived)** — `send` emits `key = some _`.
This is the one variant where `send` produces an epoch secret.
Uses liveness axiom for `send_ct1_chunk` (complex: RNG + MLKEM). -/
@[step]
theorem v1.chunked.states.States.send_HeaderReceived_key_some
    {R : Type} (rng_inst : rand.rng.Rng R) (crypto_inst : rand_core.CryptoRng R)
    (state : v1.chunked.send_ct.HeaderReceived) (rng : R) :
    v1.chunked.states.States.send rng_inst crypto_inst
      (v1.chunked.states.States.HeaderReceived state) rng ⦃ r =>
      ∃ s, r.1 = core.result.Result.Ok s ∧ s.key.isSome ⦄ := by
  unfold v1.chunked.states.States.send v1.chunked.send_ct.HeaderReceived.epoch
  step*

end spqr
