/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Spqr.Specs.External

/-! # PROP-26 + PROP-39: Epoch Guards for `States.recv`

Specifications and proofs for epoch guards on `States.recv`
(PROP-26 and PROP-39 from `docs/mlkembraid_spec/3_protocol.md`).

**PROP-26:** In the Ct2Sampled state, messages from future epochs beyond
`epoch + 1` are rejected with `EpochOutOfRange`.

**PROP-39:** For all 10 non-Ct2Sampled state variants, any message with
`msg.epoch > state.epoch` is rejected with `EpochOutOfRange`.

**Source**: spqr/src/v1/chunked/states.rs (lines 275-532)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/-! ## Helper specs -/

/-- `OrdU64.cmp` lifted into `Result` yields `compare` on `.val`. -/
@[step]
theorem OrdU64_cmp_spec (x y : Std.U64) :
    lift (core.cmp.impls.OrdU64.cmp x y)
      ⦃ o => o = compare x.val y.val ⦄ := by
  simp only [lift, core.cmp.impls.OrdU64.cmp, WP.spec, WP.theta, WP.wp_return]

/-! ## PROP-26: Main theorem -/

/-- **PROP-26 — Ct2Sampled future epoch guard.**

When `msg.epoch > state.uc.epoch + 1` (at the ℕ level), `States.recv`
on a `Ct2Sampled` state returns `Err(EpochOutOfRange msg.epoch)`. -/
@[step]
theorem v1.chunked.states.States.recv_Ct2Sampled_future_epoch_guard
    (state : v1.chunked.send_ct.Ct2Sampled)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch.val > state.uc.epoch.val + 1) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.Ct2Sampled state) msg ⦃ r =>
      r = core.result.Result.Err (Error.EpochOutOfRange msg.epoch) ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ct.Ct2Sampled.epoch
  step*
  -- .lt branch: impossible (msg.epoch > state.uc.epoch)
  exfalso
  have h_cmp : compare (↑msg.epoch : ℕ) ↑state.uc.epoch = Ordering.gt := by
    rw [Nat.compare_eq_gt]; scalar_tac
  simp_all -- terminal: derives False from contradictory Ordering hypotheses

/-! ## PROP-39: Greater-branch guards for all non-Ct2Sampled variants

For each variant, when `msg.epoch > state.epoch()`, `States.recv` returns
`Err(EpochOutOfRange msg.epoch)`. All 10 proofs follow the same pattern:
unfold `recv` + the variant's `.epoch`, run `step*`, and dismiss the
impossible `.lt` branch by contradiction on the `compare` result.
-/

private theorem gt_branch_contradiction
  {ep_msg ep_state : ℕ} {o : Ordering}
  (h_gt : ep_msg > ep_state)
  (o_post : o = compare ep_msg ep_state)
  (h_lt : o = Ordering.lt) : False := by
  have : compare ep_msg ep_state = Ordering.gt := by
    rw [Nat.compare_eq_gt]; omega
  simp_all -- terminal: derives False from contradictory Ordering hypotheses

/-- **PROP-39 (KeysUnsampled)** — Greater-branch returns `EpochOutOfRange`. -/
@[step]
theorem v1.chunked.states.States.recv_KeysUnsampled_gt_guard
    (state : v1.chunked.send_ek.KeysUnsampled)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch > state.uc.epoch) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.KeysUnsampled state) msg ⦃ r =>
      r = core.result.Result.Err (Error.EpochOutOfRange msg.epoch) ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ek.KeysUnsampled.epoch
  step*; exfalso; exact gt_branch_contradiction (by scalar_tac) o_post ‹_›

/-- **PROP-39 (KeysSampled)** — Greater-branch returns `EpochOutOfRange`. -/
@[step]
theorem v1.chunked.states.States.recv_KeysSampled_gt_guard
    (state : v1.chunked.send_ek.KeysSampled)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch > state.uc.epoch) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.KeysSampled state) msg ⦃ r =>
      r = core.result.Result.Err (Error.EpochOutOfRange msg.epoch) ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ek.KeysSampled.epoch
  step*; exfalso; exact gt_branch_contradiction (by scalar_tac) o_post ‹_›

/-- **PROP-39 (HeaderSent)** — Greater-branch returns `EpochOutOfRange`. -/
@[step]
theorem v1.chunked.states.States.recv_HeaderSent_gt_guard
    (state : v1.chunked.send_ek.HeaderSent)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch > state.uc.epoch) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.HeaderSent state) msg ⦃ r =>
      r = core.result.Result.Err (Error.EpochOutOfRange msg.epoch) ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ek.HeaderSent.epoch
  step*; exfalso; exact gt_branch_contradiction (by scalar_tac) o_post ‹_›

/-- **PROP-39 (Ct1Received)** — Greater-branch returns `EpochOutOfRange`. -/
@[step]
theorem v1.chunked.states.States.recv_Ct1Received_gt_guard
    (state : v1.chunked.send_ek.Ct1Received)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch > state.uc.epoch) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.Ct1Received state) msg ⦃ r =>
      r = core.result.Result.Err (Error.EpochOutOfRange msg.epoch) ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ek.Ct1Received.epoch
  step*; exfalso; exact gt_branch_contradiction (by scalar_tac) o_post ‹_›

/-- **PROP-39 (EkSentCt1Received)** — Greater-branch returns `EpochOutOfRange`. -/
@[step]
theorem v1.chunked.states.States.recv_EkSentCt1Received_gt_guard
    (state : v1.chunked.send_ek.EkSentCt1Received)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch > state.uc.epoch) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.EkSentCt1Received state) msg ⦃ r =>
      r = core.result.Result.Err (Error.EpochOutOfRange msg.epoch) ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ek.EkSentCt1Received.epoch
  step*; exfalso; exact gt_branch_contradiction (by scalar_tac) o_post ‹_›

/-- **PROP-39 (NoHeaderReceived)** — Greater-branch returns `EpochOutOfRange`. -/
@[step]
theorem v1.chunked.states.States.recv_NoHeaderReceived_gt_guard
    (state : v1.chunked.send_ct.NoHeaderReceived)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch > state.uc.epoch) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.NoHeaderReceived state) msg ⦃ r =>
      r = core.result.Result.Err (Error.EpochOutOfRange msg.epoch) ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ct.NoHeaderReceived.epoch
  step*; exfalso; exact gt_branch_contradiction (by scalar_tac) o_post ‹_›

/-- **PROP-39 (HeaderReceived)** — Greater-branch returns `EpochOutOfRange`. -/
@[step]
theorem v1.chunked.states.States.recv_HeaderReceived_gt_guard
    (state : v1.chunked.send_ct.HeaderReceived)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch > state.uc.epoch) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.HeaderReceived state) msg ⦃ r =>
      r = core.result.Result.Err (Error.EpochOutOfRange msg.epoch) ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ct.HeaderReceived.epoch
  step*; exfalso; exact gt_branch_contradiction (by scalar_tac) o_post ‹_›

/-- **PROP-39 (Ct1Sampled)** — Greater-branch returns `EpochOutOfRange`. -/
@[step]
theorem v1.chunked.states.States.recv_Ct1Sampled_gt_guard
    (state : v1.chunked.send_ct.Ct1Sampled)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch > state.uc.epoch) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.Ct1Sampled state) msg ⦃ r =>
      r = core.result.Result.Err (Error.EpochOutOfRange msg.epoch) ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ct.Ct1Sampled.epoch
  step*; exfalso; exact gt_branch_contradiction (by scalar_tac) o_post ‹_›

/-- **PROP-39 (EkReceivedCt1Sampled)** — Greater-branch returns `EpochOutOfRange`. -/
@[step]
theorem v1.chunked.states.States.recv_EkReceivedCt1Sampled_gt_guard
    (state : v1.chunked.send_ct.EkReceivedCt1Sampled)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch > state.uc.epoch) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.EkReceivedCt1Sampled state) msg ⦃ r =>
      r = core.result.Result.Err (Error.EpochOutOfRange msg.epoch) ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ct.EkReceivedCt1Sampled.epoch
  step*; exfalso; exact gt_branch_contradiction (by scalar_tac) o_post ‹_›

/-- **PROP-39 (Ct1Acknowledged)** — Greater-branch returns `EpochOutOfRange`. -/
@[step]
theorem v1.chunked.states.States.recv_Ct1Acknowledged_gt_guard
    (state : v1.chunked.send_ct.Ct1Acknowledged)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch > state.uc.epoch) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.Ct1Acknowledged state) msg ⦃ r =>
      r = core.result.Result.Err (Error.EpochOutOfRange msg.epoch) ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ct.Ct1Acknowledged.epoch
  step*; exfalso; exact gt_branch_contradiction (by scalar_tac) o_post ‹_›

/-! ## PROP-30: Less-branch no-op for all variants

For each variant, when `msg.epoch < state.epoch()`, `States.recv` returns
`Ok { key := none, state := self }` — a no-op. The proof pattern mirrors
PROP-39: unfold `recv` + the variant's `.epoch`, run `step*`, and dismiss
the impossible `.gt` branch by contradiction.
-/

private theorem lt_branch_contradiction
  {ep_msg ep_state : ℕ} {o : Ordering}
  (h_lt : ep_msg < ep_state)
  (o_post : o = compare ep_msg ep_state)
  (h_gt : o = Ordering.gt) : False := by
  have : compare ep_msg ep_state = Ordering.lt := by
    rw [Nat.compare_eq_lt]; omega
  simp_all -- terminal: derives False from contradictory Ordering hypotheses

/-- **PROP-30 (KeysUnsampled)** — Less-branch is no-op. -/
@[step]
theorem v1.chunked.states.States.recv_KeysUnsampled_lt_noop
    (state : v1.chunked.send_ek.KeysUnsampled)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch < state.uc.epoch) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.KeysUnsampled state) msg ⦃ r =>
      r = core.result.Result.Ok
        { key := none, state := v1.chunked.states.States.KeysUnsampled state } ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ek.KeysUnsampled.epoch
  step*; exfalso; exact lt_branch_contradiction (by scalar_tac) o_post ‹_›

/-- **PROP-30 (KeysSampled)** — Less-branch is no-op. -/
@[step]
theorem v1.chunked.states.States.recv_KeysSampled_lt_noop
    (state : v1.chunked.send_ek.KeysSampled)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch < state.uc.epoch) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.KeysSampled state) msg ⦃ r =>
      r = core.result.Result.Ok
        { key := none, state := v1.chunked.states.States.KeysSampled state } ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ek.KeysSampled.epoch
  step*; exfalso; exact lt_branch_contradiction (by scalar_tac) o_post ‹_›

/-- **PROP-30 (HeaderSent)** — Less-branch is no-op. -/
@[step]
theorem v1.chunked.states.States.recv_HeaderSent_lt_noop
    (state : v1.chunked.send_ek.HeaderSent)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch < state.uc.epoch) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.HeaderSent state) msg ⦃ r =>
      r = core.result.Result.Ok
        { key := none, state := v1.chunked.states.States.HeaderSent state } ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ek.HeaderSent.epoch
  step*; exfalso; exact lt_branch_contradiction (by scalar_tac) o_post ‹_›

/-- **PROP-30 (Ct1Received)** — Less-branch is no-op. -/
@[step]
theorem v1.chunked.states.States.recv_Ct1Received_lt_noop
    (state : v1.chunked.send_ek.Ct1Received)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch < state.uc.epoch) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.Ct1Received state) msg ⦃ r =>
      r = core.result.Result.Ok
        { key := none, state := v1.chunked.states.States.Ct1Received state } ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ek.Ct1Received.epoch
  step*; exfalso; exact lt_branch_contradiction (by scalar_tac) o_post ‹_›

/-- **PROP-30 (EkSentCt1Received)** — Less-branch is no-op. -/
@[step]
theorem v1.chunked.states.States.recv_EkSentCt1Received_lt_noop
    (state : v1.chunked.send_ek.EkSentCt1Received)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch < state.uc.epoch) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.EkSentCt1Received state) msg ⦃ r =>
      r = core.result.Result.Ok
        { key := none,
          state := v1.chunked.states.States.EkSentCt1Received state } ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ek.EkSentCt1Received.epoch
  step*; exfalso; exact lt_branch_contradiction (by scalar_tac) o_post ‹_›

/-- **PROP-30 (NoHeaderReceived)** — Less-branch is no-op. -/
@[step]
theorem v1.chunked.states.States.recv_NoHeaderReceived_lt_noop
    (state : v1.chunked.send_ct.NoHeaderReceived)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch < state.uc.epoch) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.NoHeaderReceived state) msg ⦃ r =>
      r = core.result.Result.Ok
        { key := none, state := v1.chunked.states.States.NoHeaderReceived state } ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ct.NoHeaderReceived.epoch
  step*; exfalso; exact lt_branch_contradiction (by scalar_tac) o_post ‹_›

/-- **PROP-30 (HeaderReceived)** — Less-branch is no-op. -/
@[step]
theorem v1.chunked.states.States.recv_HeaderReceived_lt_noop
    (state : v1.chunked.send_ct.HeaderReceived)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch < state.uc.epoch) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.HeaderReceived state) msg ⦃ r =>
      r = core.result.Result.Ok
        { key := none, state := v1.chunked.states.States.HeaderReceived state } ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ct.HeaderReceived.epoch
  step*; exfalso; exact lt_branch_contradiction (by scalar_tac) o_post ‹_›

/-- **PROP-30 (Ct1Sampled)** — Less-branch is no-op. -/
@[step]
theorem v1.chunked.states.States.recv_Ct1Sampled_lt_noop
    (state : v1.chunked.send_ct.Ct1Sampled)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch < state.uc.epoch) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.Ct1Sampled state) msg ⦃ r =>
      r = core.result.Result.Ok
        { key := none, state := v1.chunked.states.States.Ct1Sampled state } ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ct.Ct1Sampled.epoch
  step*; exfalso; exact lt_branch_contradiction (by scalar_tac) o_post ‹_›

/-- **PROP-30 (EkReceivedCt1Sampled)** — Less-branch is no-op. -/
@[step]
theorem v1.chunked.states.States.recv_EkReceivedCt1Sampled_lt_noop
    (state : v1.chunked.send_ct.EkReceivedCt1Sampled)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch < state.uc.epoch) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.EkReceivedCt1Sampled state) msg ⦃ r =>
      r = core.result.Result.Ok
        { key := none,
          state := v1.chunked.states.States.EkReceivedCt1Sampled state } ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ct.EkReceivedCt1Sampled.epoch
  step*; exfalso; exact lt_branch_contradiction (by scalar_tac) o_post ‹_›

/-- **PROP-30 (Ct1Acknowledged)** — Less-branch is no-op. -/
@[step]
theorem v1.chunked.states.States.recv_Ct1Acknowledged_lt_noop
    (state : v1.chunked.send_ct.Ct1Acknowledged)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch < state.uc.epoch) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.Ct1Acknowledged state) msg ⦃ r =>
      r = core.result.Result.Ok
        { key := none, state := v1.chunked.states.States.Ct1Acknowledged state } ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ct.Ct1Acknowledged.epoch
  step*; exfalso; exact lt_branch_contradiction (by scalar_tac) o_post ‹_›

/-- **PROP-30 (Ct2Sampled)** — Less-branch is no-op. -/
@[step]
theorem v1.chunked.states.States.recv_Ct2Sampled_lt_noop
    (state : v1.chunked.send_ct.Ct2Sampled)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch < state.uc.epoch) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.Ct2Sampled state) msg ⦃ r =>
      r = core.result.Result.Ok
        { key := none, state := v1.chunked.states.States.Ct2Sampled state } ⦄ := by
  unfold v1.chunked.states.States.recv v1.chunked.send_ct.Ct2Sampled.epoch
  step*
  all_goals (exfalso; exact lt_branch_contradiction (by scalar_tac) o_post ‹_›)

end spqr
