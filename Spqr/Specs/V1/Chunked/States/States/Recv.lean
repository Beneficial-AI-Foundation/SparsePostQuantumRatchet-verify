/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Braid.StateMachine.EpochDispatch
public import Spqr.Specs.V1.Chunked.SendEk.KeysSampled.RecvCt1Chunk
public import Spqr.Specs.V1.Chunked.SendEk.HeaderSent.RecvCt1Chunk
public import Spqr.Specs.V1.Chunked.SendEk.Ct1Received.RecvCt2Chunk
public import Spqr.Specs.V1.Chunked.SendEk.EkSentCt1Received.RecvCt2Chunk
public import Spqr.Specs.V1.Chunked.SendCt.NoHeaderReceived.RecvHdrChunk
public import Spqr.Specs.V1.Chunked.SendCt.Ct1Sampled.RecvEkChunk
public import Spqr.Specs.V1.Chunked.SendCt.EkReceivedCt1Sampled.RecvCt1Ack
public import Spqr.Specs.V1.Chunked.SendCt.Ct1Acknowledged.RecvEkChunk
import Spqr.Auxiliary.Aeneas.Result
import Spqr.Auxiliary.Aeneas.SpecImpExists
/-!
# Spec theorem for `spqr::v1::chunked::states::{States}::recv`

`States::recv` is the receive dispatcher of the *chunked* V1 ratchet.  Given the current state
`self : States` (one of the eleven variants of the send-ek / send-ct state machine) and an
incoming `msg : Message`, every arm first compares `msg.epoch` with the epoch of the state's
unchunked payload (`States.epochOf self`):

  * `msg.epoch < epoch`: the message is stale — the state is returned unchanged, no key;
  * `msg.epoch > epoch`: `Err (EpochOutOfRange msg.epoch)`, except in `Ct2Sampled` when
    `msg.epoch = epoch + 1`, where the state advances to `KeysUnsampled` at the new epoch via
    `Ct2Sampled::recv_next_epoch` (no key);
  * `msg.epoch = epoch`: the payload is dispatched to the per-state chunk handler
    (`recv_ct1_chunk`, `recv_ct2_chunk`, `recv_hdr_chunk`, `recv_ek_chunk`, `recv_ct1_ack`);
    the handler's outcome is wrapped into the successor `States` variant, a `?`-propagated
    `Err` is returned as is, and a payload the state does not expect leaves it unchanged.  Only
    `EkSentCt1Received` on a completing `Ct2` chunk emits a key (`key = some sec`).

The handlers carry well-formedness preconditions (decoder validity, buffer sizes, …) that a
bare `States` value does not provide, so — as for `spqr.recv` (`Spqr/Specs/Lib/Recv.lean`) —
the total contract `recv_spec` takes them as an explicit input predicate (`recvPre`, i.e.
`recvHandlerPre` for the same-epoch pair that is dispatched, assembled from the hypotheses of
the handlers' `*_spec_concrete` theorems), proves that the call returns a value under them
(`recv_eq_ok_of_eq`), and pins the result, path by path, to the value returned by the handler
(`recv_spec_of_eq`, `recvPost`).  The epoch-mismatch paths call no handler apart from
`recv_next_epoch`, which is total; `recv_spec_of_ne` states them without any hypothesis.

The epoch-level equations are shared with the ML-KEM Braid §2.5 development: `States.epochOf`,
`recv_of_lt`, `recv_of_gt` and `recv_Ct2Sampled_next_epoch` are reused from
`Spqr.Specs.Braid.StateMachine.EpochDispatch` rather than re-proved here.

**Source**: spqr/src/v1/chunked/states.rs (lines 275:4-533:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr
open core.result.Result.Insts.CoreOpsTry (branch_eq_continue branch_eq_break branch_Ok branch_Err)
open core.result.Result.Insts.CoreOpsTry_traitFromResidualResult (from_residual_same
  from_residual_same_eq_ok)

namespace spqr.v1.chunked.states.States

/-! ## Postcondition -/

/-- Wraps a handler outcome into the dispatcher's result: an `Ok a` becomes `Ok (f a)`, an
`Err e` (propagated by `?` in the Rust source) is returned unchanged. -/
def liftRecv {α : Type} (f : α → Recv) : core.result.Result α Error →
    core.result.Result Recv Error
  | .Ok a => .Ok (f a)
  | .Err e => .Err e

/-- The successor of `Ct1Sampled` for each outcome of `Ct1Sampled::recv_ek_chunk`
(src/v1/chunked/states.rs, lines 426-451). -/
def ct1SampledNext : send_ct.Ct1SampledRecvChunk → Recv
  | .StillReceivingStillSending s => { key := none, state := .Ct1Sampled s }
  | .StillReceiving s => { key := none, state := .Ct1Acknowledged s }
  | .StillSending s => { key := none, state := .EkReceivedCt1Sampled s }
  | .Done s => { key := none, state := .Ct2Sampled s }

/-- The successor of `Ct1Acknowledged` for each outcome of `Ct1Acknowledged::recv_ek_chunk`
(src/v1/chunked/states.rs, lines 497-507). -/
def ct1AcknowledgedNext : send_ct.Ct1AcknowledgedRecvChunk → Recv
  | .StillReceiving s => { key := none, state := .Ct1Acknowledged s }
  | .Done s => { key := none, state := .Ct2Sampled s }

/-- Postcondition of `States::recv` on a message from the state's own epoch
(`msg.epoch = States.epochOf self`).  For every state / payload pair the dispatcher acts on,
the result is pinned to the value returned by the corresponding handler: the handler is called
with `msg.epoch` and the payload's chunk, an `Ok` outcome is wrapped into the successor state
(no key, except `EkSentCt1Received` on a completing `Ct2` chunk which returns the epoch
secret), and an `Err` outcome is propagated.  Every other pair leaves the state unchanged and
emits no key. -/
def recvEqPost (self : States) (msg : Message) (result : core.result.Result Recv Error) :
    Prop :=
  match self, msg.payload with
  | .KeysSampled st, .Ct1 chunk =>
      ∃ hs, send_ek.KeysSampled.recv_ct1_chunk st msg.epoch chunk = ok hs ∧
        result = .Ok { key := none, state := .HeaderSent hs }
  | .HeaderSent st, .Ct1 chunk =>
      ∃ r, send_ek.HeaderSent.recv_ct1_chunk st msg.epoch chunk = ok r ∧
        result = .Ok { key := none, state :=
          match r with
          | .StillReceiving s => .HeaderSent s
          | .Done s => .Ct1Received s }
  | .Ct1Received st, .Ct2 chunk =>
      ∃ escr, send_ek.Ct1Received.recv_ct2_chunk st msg.epoch chunk = ok escr ∧
        result = .Ok { key := none, state := .EkSentCt1Received escr }
  | .EkSentCt1Received st, .Ct2 chunk =>
      ∃ r, send_ek.EkSentCt1Received.recv_ct2_chunk st msg.epoch chunk = ok r ∧
        result = liftRecv (fun
          | .StillReceiving s => { key := none, state := .EkSentCt1Received s }
          | .Done (s, sec) => { key := some sec, state := .NoHeaderReceived s }) r
  | .NoHeaderReceived st, .Hdr chunk =>
      ∃ r, send_ct.NoHeaderReceived.recv_hdr_chunk st msg.epoch chunk = ok r ∧
        result = liftRecv (fun
          | .StillReceiving s => { key := none, state := .NoHeaderReceived s }
          | .Done s => { key := none, state := .HeaderReceived s }) r
  | .Ct1Sampled st, .Ek chunk =>
      ∃ r, send_ct.Ct1Sampled.recv_ek_chunk st msg.epoch chunk false = ok r ∧
        result = liftRecv ct1SampledNext r
  | .Ct1Sampled st, .EkCt1Ack chunk =>
      ∃ r, send_ct.Ct1Sampled.recv_ek_chunk st msg.epoch chunk true = ok r ∧
        result = liftRecv ct1SampledNext r
  | .EkReceivedCt1Sampled st, .EkCt1Ack _ =>
      ∃ cs, send_ct.EkReceivedCt1Sampled.recv_ct1_ack st msg.epoch = ok cs ∧
        result = .Ok { key := none, state := .Ct2Sampled cs }
  | .EkReceivedCt1Sampled st, .Ct1Ack true =>
      ∃ cs, send_ct.EkReceivedCt1Sampled.recv_ct1_ack st msg.epoch = ok cs ∧
        result = .Ok { key := none, state := .Ct2Sampled cs }
  | .Ct1Acknowledged st, .Ek chunk =>
      ∃ r, send_ct.Ct1Acknowledged.recv_ek_chunk st msg.epoch chunk = ok r ∧
        result = liftRecv ct1AcknowledgedNext r
  | .Ct1Acknowledged st, .EkCt1Ack chunk =>
      ∃ r, send_ct.Ct1Acknowledged.recv_ek_chunk st msg.epoch chunk = ok r ∧
        result = liftRecv ct1AcknowledgedNext r
  | _, _ => result = .Ok { key := none, state := self }

/-- Postcondition of `States::recv`, one clause per outcome of the epoch comparison:

  * `msg.epoch < epochOf self`: unchanged state, no key;
  * `msg.epoch = epochOf self`: `recvEqPost`;
  * `msg.epoch > epochOf self`: `Err (EpochOutOfRange msg.epoch)`, except in `Ct2Sampled st`
    with `msg.epoch = st.uc.epoch + 1`, where the result is `KeysUnsampled` at `msg.epoch` with
    the authenticator of `st` and no key. -/
def recvPost (self : States) (msg : Message) (result : core.result.Result Recv Error) : Prop :=
  (msg.epoch.val < self.epochOf.val → result = .Ok { key := none, state := self }) ∧
  (msg.epoch = self.epochOf → recvEqPost self msg result) ∧
  (self.epochOf.val < msg.epoch.val →
    match self with
    | .Ct2Sampled st =>
        if msg.epoch.val = st.uc.epoch.val + 1 then
          result = .Ok { key := none, state := .KeysUnsampled ⟨⟨msg.epoch, st.uc.auth⟩⟩ }
        else result = .Err (Error.EpochOutOfRange msg.epoch)
    | _ => result = .Err (Error.EpochOutOfRange msg.epoch))

/-- **Only `EkSentCt1Received` emits a key.**  If a result satisfying `recvPost self msg`
carries `key = some sec`, then `self = EkSentCt1Received st`, the message is from the state's
own epoch with a `Ct2` chunk, and `EkSentCt1Received::recv_ct2_chunk` completed with
`Done (s, sec)` — the new state being `NoHeaderReceived s`.  This is the lemma callers of
`recv_spec` (e.g. `spqr.recv`, whose `Chain::add_epoch` precondition is only needed when a key
is emitted) use to confine the key-emitting case to a single handler path. -/
theorem key_some_of_recvPost (self : States) (msg : Message) (r : Recv) (sec : EpochSecret)
    (hpost : recvPost self msg (.Ok r)) (hk : r.key = some sec) :
    ∃ st chunk s, self = .EkSentCt1Received st ∧ msg.payload = .Ct2 chunk ∧
      msg.epoch = st.uc.epoch ∧
      send_ek.EkSentCt1Received.recv_ct2_chunk st msg.epoch chunk = ok (.Ok (.Done (s, sec))) ∧
      r = { key := some sec, state := .NoHeaderReceived s } := by
  obtain ⟨hlt, heq, hgt⟩ := hpost
  rcases Nat.lt_trichotomy msg.epoch.val self.epochOf.val with h | h | h
  · -- stale message: state unchanged, no key
    cases hlt h; cases hk
  · -- same epoch: only the `EkSentCt1Received` / `Ct2` / `Done` outcome carries a key
    have hep : msg.epoch = self.epochOf := UScalar.eq_of_val_eq h
    have h' := heq hep
    obtain ⟨e, p⟩ := msg
    cases self <;> rcases p with _ | c | c | c | (_ | _) | c | c <;>
      simp only [recvEqPost] at h'
    case EkSentCt1Received.Ct2 st =>
      obtain ⟨res, hres, hr⟩ := h'
      rcases res with (_ | ⟨s, sec'⟩) | err <;> simp only [liftRecv] at hr <;> cases hr
      · cases hk
      · cases hk
        exact ⟨st, c, s, rfl, rfl, hep, hres, rfl⟩
    -- handlers returning a plain value: `KeysSampled`, `Ct1Received`, `EkReceivedCt1Sampled`
    case KeysSampled.Ct1 | Ct1Received.Ct2 | EkReceivedCt1Sampled.EkCt1Ack
      | EkReceivedCt1Sampled.Ct1Ack.true =>
      obtain ⟨_, -, hr⟩ := h'; cases hr; cases hk
    -- `HeaderSent::recv_ct1_chunk` returns the enum directly
    case HeaderSent.Ct1 =>
      obtain ⟨res, -, hr⟩ := h'; cases res <;> cases hr <;> cases hk
    -- handlers behind `?`: `NoHeaderReceived`, `Ct1Sampled`, `Ct1Acknowledged`
    case NoHeaderReceived.Hdr | Ct1Sampled.Ek | Ct1Sampled.EkCt1Ack | Ct1Acknowledged.Ek
      | Ct1Acknowledged.EkCt1Ack =>
      obtain ⟨res, -, hr⟩ := h'
      rcases res with v | err
      · cases v <;> simp only [liftRecv, ct1SampledNext, ct1AcknowledgedNext] at hr <;>
          cases hr <;> cases hk
      · simp only [liftRecv] at hr; cases hr
    -- pairs the dispatcher does not act on
    all_goals cases h'; cases hk
  · -- their epoch is ahead: `Err`, or `KeysUnsampled` without key
    have h' := hgt h
    cases self <;> simp only at h' <;> (try split at h') <;> cases h'
    -- `Ct2Sampled` stepping to `KeysUnsampled`: no key
    cases hk

/-! ## Preconditions -/

/-- Precondition of `Ct1Sampled::recv_ek_chunk` / `Ct1Acknowledged::recv_ek_chunk` on the
unchunked `Ct1Sent` payload `uc` and the `ek` decoder `pd` for an incoming `chunk`: exactly the
hypotheses of `recv_ek_chunk_spec_concrete` (minus `h_epoch`). -/
def recvEkChunkPre (uc : unchunked.send_ct.Ct1Sent) (pd : encoding.polynomial.PolyDecoder)
    (chunk : encoding.Chunk) : Prop :=
  chunk.index * 16 + 16 ≤ Usize.max ∧
  (∀ (k : Nat), k < 16 → (pd.pts[k]!).length + 17 ≤ Usize.max) ∧
  encoding.polynomial.PolyDecoder.PointsValid pd.pts ∧
  pd.pts_needed.val = 576 ∧
  uc.es.length = 2080 ∧
  uc.auth.mac_key.length ≤ U32.max ∧
  uc.ct1.length + 128 + 43 ≤ U32.max

/-- Preconditions of the handler that `States::recv` calls on a same-epoch message, one field
per acting state / payload pair, guarded by the shape of `self` and `msg.payload`; a pair not
listed here calls no handler.  Each field is exactly the hypothesis list of the handler's spec
theorem — `*_spec_concrete` where one exists, otherwise `*_spec` (`KeysSampled`, `Ct1Received`,
`EkReceivedCt1Sampled`) — minus `h_epoch`, which the dispatcher establishes: chunk-index
overflow bounds, `PolyDecoder` well-formedness (`PointsValid`, per-set capacity, `pts_needed`),
the values of the opaque ML-KEM size constants, and the buffer lengths / scalar bounds of the
unchunked payload. -/
structure recvHandlerPre (self : States) (msg : Message) : Prop where
  /-- `KeysSampled::recv_ct1_chunk` (`recv_ct1_chunk_spec`). -/
  keysSampled_ct1 : ∀ st chunk, self = .KeysSampled st → msg.payload = .Ct1 chunk →
    incremental_mlkem768.CIPHERTEXT1_SIZE ⦃ (r : Usize) => r.val = 960 ⦄ ∧
    st.uc.ek.length = 1152
  /-- `HeaderSent::recv_ct1_chunk` (`recv_ct1_chunk_spec_concrete`). -/
  headerSent_ct1 : ∀ st chunk, self = .HeaderSent st → msg.payload = .Ct1 chunk →
    (∀ (k : Nat), k < 16 → (st.receiving_ct1.pts[k]!).length + 17 ≤ Usize.max) ∧
    encoding.polynomial.PolyDecoder.PointsValid st.receiving_ct1.pts ∧
    st.receiving_ct1.pts_needed.val = 480
  /-- `Ct1Received::recv_ct2_chunk` (`recv_ct2_chunk_spec`). -/
  ct1Received_ct2 : ∀ st chunk, self = .Ct1Received st → msg.payload = .Ct2 chunk →
    chunk.index * 16 + 16 ≤ Usize.max ∧
    incremental_mlkem768.CIPHERTEXT2_SIZE ⦃ (r : Usize) => r.val = 128 ⦄
  /-- `EkSentCt1Received::recv_ct2_chunk` (`recv_ct2_chunk_spec_concrete`). -/
  ekSentCt1Received_ct2 : ∀ st chunk, self = .EkSentCt1Received st →
    msg.payload = .Ct2 chunk →
    chunk.index * 16 + 16 ≤ Usize.max ∧
    (∀ (k : Nat), k < 16 → (st.receiving_ct2.pts[k]!).length + 17 ≤ Usize.max) ∧
    encoding.polynomial.PolyDecoder.PointsValid st.receiving_ct2.pts ∧
    st.receiving_ct2.pts_needed.val = 80 ∧
    incremental_mlkem768.CIPHERTEXT2_SIZE ⦃ (r : Usize) => r.val = 128 ⦄ ∧
    st.uc.dk.length = 2400 ∧
    st.uc.ct1.length = 960 ∧
    st.uc.epoch < U64.max ∧
    st.uc.auth.root_key.length + 32 ≤ Usize.max
  /-- `NoHeaderReceived::recv_hdr_chunk` (`recv_hdr_chunk_spec_concrete`). -/
  noHeaderReceived_hdr : ∀ st chunk, self = .NoHeaderReceived st → msg.payload = .Hdr chunk →
    chunk.index * 16 + 16 ≤ Usize.max ∧
    (∀ (k : Nat), k < 16 → (st.receiving_hdr.pts[k]!).length + 17 ≤ Usize.max) ∧
    encoding.polynomial.PolyDecoder.PointsValid st.receiving_hdr.pts ∧
    st.receiving_hdr.pts_needed.val = 48 ∧
    incremental_mlkem768.ENCAPSULATION_KEY_SIZE ⦃ (r : Usize) => r.val = 1152 ⦄ ∧
    st.uc.auth.mac_key.length ≤ U32.max
  /-- `Ct1Sampled::recv_ek_chunk` on `Ek` / `EkCt1Ack` (`recv_ek_chunk_spec_concrete`). -/
  ct1Sampled_ek : ∀ st chunk, self = .Ct1Sampled st →
    (msg.payload = .Ek chunk ∨ msg.payload = .EkCt1Ack chunk) →
    recvEkChunkPre st.uc st.receiving_ek chunk
  /-- `EkReceivedCt1Sampled::recv_ct1_ack` on `EkCt1Ack` / `Ct1Ack true`
  (`recv_ct1_ack_spec`). -/
  ekReceivedCt1Sampled_ack : ∀ st, self = .EkReceivedCt1Sampled st →
    ((∃ chunk, msg.payload = .EkCt1Ack chunk) ∨ msg.payload = .Ct1Ack true) →
    st.uc.ek.length = 1152 ∧
    st.uc.es.length = 2080 ∧
    st.uc.auth.mac_key.length ≤ U32.max ∧
    st.uc.ct1.length + 128 + 43 ≤ U32.max
  /-- `Ct1Acknowledged::recv_ek_chunk` on `Ek` / `EkCt1Ack` (`recv_ek_chunk_spec_concrete`). -/
  ct1Acknowledged_ek : ∀ st chunk, self = .Ct1Acknowledged st →
    (msg.payload = .Ek chunk ∨ msg.payload = .EkCt1Ack chunk) →
    recvEkChunkPre st.uc st.receiving_ek chunk

/-- Inputs under which `States::recv` does not panic: the handler preconditions are only
needed when the message is from the state's own epoch, the only case in which a handler is
called. -/
def recvPre (self : States) (msg : Message) : Prop :=
  msg.epoch = self.epochOf → recvHandlerPre self msg

/-- `recvPre` is vacuous on an epoch mismatch. -/
theorem recvPre_of_ne (self : States) (msg : Message) (h : msg.epoch ≠ self.epochOf) :
    recvPre self msg := fun heq => absurd heq h

/-! ## The same-epoch dispatch -/

/-- If `msg` is from the epoch of `self` and `recv self msg` returns `r`, then `r` satisfies
`recvEqPost self msg`.  One case per state / payload pair; the pairs with a `?`-propagating
handler are closed by inverting `branch` / `from_residual`. -/
theorem recvEqPost_of_eq (self : States) (msg : Message) (r : core.result.Result Recv Error)
    (h : msg.epoch = self.epochOf) (hr : recv self msg = ok r) : recvEqPost self msg r := by
  obtain ⟨e, p⟩ := msg
  cases self <;> rcases p with _ | c | c | c | (_ | _) | c | c <;>
    simp only [States.epochOf] at h <;> subst h <;>
    simp only [recv, send_ek.KeysUnsampled.epoch, send_ek.KeysSampled.epoch,
      send_ek.HeaderSent.epoch, send_ek.Ct1Received.epoch, send_ek.EkSentCt1Received.epoch,
      send_ct.NoHeaderReceived.epoch, send_ct.HeaderReceived.epoch, send_ct.Ct1Sampled.epoch,
      send_ct.EkReceivedCt1Sampled.epoch, send_ct.Ct1Acknowledged.epoch,
      send_ct.Ct2Sampled.epoch, lift, core.cmp.impls.OrdU64.cmp, bind_ok,
      Nat.compare_eq_eq.2 rfl, Bool.false_eq_true, ite_false, ite_true] at hr
  -- pairs the dispatcher does not act on: the state is returned unchanged
  all_goals try (rw [ok.injEq] at hr; subst hr; rfl)
  -- `Ct1Sampled` desugars `let (chunk, ack) = match msg.payload { … }` into a nested match
  -- that `simp only` leaves folded; the `change` states its value for the non-acting payloads.
  -- It depends on the extracted shape of that pattern and must be revisited on re-extraction.
  case Ct1Sampled.None st | Ct1Sampled.Hdr st | Ct1Sampled.Ct1Ack.false st
      | Ct1Sampled.Ct1Ack.true st | Ct1Sampled.Ct1 st | Ct1Sampled.Ct2 st =>
    change ok (core.result.Result.Ok { key := none, state := States.Ct1Sampled st }) = ok r at hr
    rw [ok.injEq] at hr; subst hr; rfl
  -- handlers without `?`: `KeysSampled`, `Ct1Received`, `EkReceivedCt1Sampled`
  case KeysSampled.Ct1 | Ct1Received.Ct2 | EkReceivedCt1Sampled.EkCt1Ack
    | EkReceivedCt1Sampled.Ct1Ack.true =>
    obtain ⟨_, hres, hr⟩ := bind_eq_ok.1 hr
    rw [ok.injEq] at hr; subst hr
    exact ⟨_, hres, rfl⟩
  -- `HeaderSent::recv_ct1_chunk` returns the enum directly
  case HeaderSent.Ct1 =>
    obtain ⟨res, hres, hr⟩ := bind_eq_ok.1 hr
    cases res <;> rw [ok.injEq] at hr <;> subst hr <;> exact ⟨_, hres, rfl⟩
  -- `EkSentCt1Received::recv_ct2_chunk?`: the `Done` outcome carries a pair
  case EkSentCt1Received.Ct2 =>
    obtain ⟨res, hres, hr⟩ := bind_eq_ok.1 hr
    simp only [bind_eq_ok] at hr
    obtain ⟨cf, hcf, hr⟩ := hr
    refine ⟨res, hres, ?_⟩
    cases cf with
    | Break rs =>
      obtain ⟨err, rfl, rfl⟩ := branch_eq_break hcf
      exact from_residual_same_eq_ok hr
    | Continue val =>
      obtain rfl := branch_eq_continue hcf
      cases val with
      | StillReceiving s => rw [ok.injEq] at hr; subst hr; rfl
      | Done p =>
        obtain ⟨s, sec⟩ := p
        change ok (core.result.Result.Ok
          { key := some sec, state := States.NoHeaderReceived s }) = ok r at hr
        rw [ok.injEq] at hr; subst hr; rfl
  -- remaining handlers behind `?`
  all_goals
    obtain ⟨res, hres, hr⟩ := bind_eq_ok.1 hr
    simp only [bind_eq_ok] at hr
    obtain ⟨cf, hcf, hr⟩ := hr
    refine ⟨res, hres, ?_⟩
    cases cf with
    | Break rs =>
      obtain ⟨err, rfl, rfl⟩ := branch_eq_break hcf
      exact from_residual_same_eq_ok hr
    | Continue val =>
      obtain rfl := branch_eq_continue hcf
      cases val <;> rw [ok.injEq] at hr <;> subst hr <;> rfl

/-- Under the handler preconditions, `recv` on a same-epoch message returns a value: each
acting pair is closed by the `*_spec_concrete` theorem of its handler (which yields the
handler's return value), every other pair returns `ok` directly. -/
theorem recv_eq_ok_of_eq (self : States) (msg : Message) (h : msg.epoch = self.epochOf)
    (hpre : recvHandlerPre self msg) : ∃ r, recv self msg = ok r := by
  obtain ⟨e, p⟩ := msg
  obtain ⟨hKS, hHS, hC1R, hESC, hNHR, hC1S, hERC, hC1A⟩ := hpre
  cases self <;> rcases p with _ | c | c | c | (_ | _) | c | c <;>
    simp only [States.epochOf] at h <;> subst h <;>
    simp only [recv, send_ek.KeysUnsampled.epoch, send_ek.KeysSampled.epoch,
      send_ek.HeaderSent.epoch, send_ek.Ct1Received.epoch, send_ek.EkSentCt1Received.epoch,
      send_ct.NoHeaderReceived.epoch, send_ct.HeaderReceived.epoch, send_ct.Ct1Sampled.epoch,
      send_ct.EkReceivedCt1Sampled.epoch, send_ct.Ct1Acknowledged.epoch,
      send_ct.Ct2Sampled.epoch, lift, core.cmp.impls.OrdU64.cmp, bind_ok,
      Nat.compare_eq_eq.2 rfl, Bool.false_eq_true, ite_false, ite_true]
  -- pairs the dispatcher does not act on: `ok` directly (up to the `let (chunk, ack)` pattern)
  all_goals try exact ⟨_, rfl⟩
  case KeysSampled.Ct1 st =>
    obtain ⟨h1, h2⟩ := hKS st c rfl rfl
    obtain ⟨v, hv, -⟩ :=
      WP.spec_imp_exists (send_ek.KeysSampled.recv_ct1_chunk_spec st _ c rfl h1 h2)
    exact ⟨_, by rw [hv, bind_ok]⟩
  case HeaderSent.Ct1 st =>
    obtain ⟨h1, h2, h3⟩ := hHS st c rfl rfl
    obtain ⟨v, hv, -⟩ := WP.spec_imp_exists
      (send_ek.HeaderSent.recv_ct1_chunk_spec_concrete st _ c rfl h1 h2 h3)
    rw [hv, bind_ok]
    cases v <;> exact ⟨_, rfl⟩
  case Ct1Received.Ct2 st =>
    obtain ⟨h1, h2⟩ := hC1R st c rfl rfl
    obtain ⟨v, hv, -⟩ :=
      WP.spec_imp_exists (send_ek.Ct1Received.recv_ct2_chunk_spec st _ c rfl h1 h2)
    exact ⟨_, by rw [hv, bind_ok]⟩
  case EkSentCt1Received.Ct2 st =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hESC st c rfl rfl
    obtain ⟨r, hr, -⟩ := WP.spec_imp_exists
      (send_ek.EkSentCt1Received.recv_ct2_chunk_spec_concrete st _ c rfl h1 h2 h3 h4 h5 h6 h7
        h8 h9)
    rw [hr, bind_ok]
    rcases r with v | e
    · rw [branch_Ok, bind_ok]
      rcases v with _ | ⟨_, _⟩ <;> exact ⟨_, rfl⟩
    · rw [branch_Err, bind_ok]; exact ⟨_, from_residual_same e⟩
  case NoHeaderReceived.Hdr st =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hNHR st c rfl rfl
    obtain ⟨r, hr, -⟩ := WP.spec_imp_exists
      (send_ct.NoHeaderReceived.recv_hdr_chunk_spec_concrete st _ c rfl h1 h2 h3 h4 h5 h6)
    rw [hr, bind_ok]
    rcases r with v | e
    · rw [branch_Ok, bind_ok]
      rcases v with _ | _ <;> exact ⟨_, rfl⟩
    · rw [branch_Err, bind_ok]; exact ⟨_, from_residual_same e⟩
  case Ct1Sampled.Ek st | Ct1Sampled.EkCt1Ack st =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
      hC1S st c rfl (by first | exact .inl rfl | exact .inr rfl)
    obtain ⟨r, hr, -⟩ := WP.spec_imp_exists
      (send_ct.Ct1Sampled.recv_ek_chunk_spec_concrete st _ c _ rfl h1 h2 h3 h4 h5 h6 h7)
    change ∃ r', Std.bind (send_ct.Ct1Sampled.recv_ek_chunk st st.uc.epoch c _) _ = ok r'
    rw [hr, bind_ok]
    rcases r with v | e
    · rw [branch_Ok, bind_ok]
      rcases v with _ | _ | _ | _ <;> exact ⟨_, rfl⟩
    · rw [branch_Err, bind_ok]; exact ⟨_, from_residual_same e⟩
  case EkReceivedCt1Sampled.EkCt1Ack st | EkReceivedCt1Sampled.Ct1Ack.true st =>
    obtain ⟨h1, h2, h3, h4⟩ :=
      hERC st rfl (by first | exact .inl ⟨_, rfl⟩ | exact .inr rfl)
    obtain ⟨v, hv, -⟩ := WP.spec_imp_exists
      (send_ct.EkReceivedCt1Sampled.recv_ct1_ack_spec st _ rfl h1 h2 h3 h4)
    exact ⟨_, by rw [hv, bind_ok]⟩
  case Ct1Acknowledged.Ek st | Ct1Acknowledged.EkCt1Ack st =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
      hC1A st c rfl (by first | exact .inl rfl | exact .inr rfl)
    obtain ⟨r, hr, -⟩ := WP.spec_imp_exists
      (send_ct.Ct1Acknowledged.recv_ek_chunk_spec_concrete st _ c rfl h1 h2 h3 h4 h5 h6 h7)
    rw [hr, bind_ok]
    rcases r with v | e
    · rw [branch_Ok, bind_ok]
      rcases v with _ | _ <;> exact ⟨_, rfl⟩
    · rw [branch_Err, bind_ok]; exact ⟨_, from_residual_same e⟩

/-- **Same-epoch lemma for `spqr.v1.chunked.states.States.recv`**: under the handler
preconditions, `recv` on a message from the state's own epoch returns a value satisfying
`recvEqPost self msg` — the result is pinned to the value returned by the handler of the
matched state / payload pair. -/
theorem recv_spec_of_eq (self : States) (msg : Message) (h : msg.epoch = self.epochOf)
    (hpre : recvHandlerPre self msg) :
    recv self msg ⦃ (result : core.result.Result Recv Error) => recvEqPost self msg result ⦄ := by
  obtain ⟨r, hr⟩ := recv_eq_ok_of_eq self msg h hpre
  rw [hr, WP.spec_ok]
  exact recvEqPost_of_eq self msg r h hr

/-! ## The epoch-mismatch dispatch -/

/-- **Epoch-mismatch lemma for `spqr.v1.chunked.states.States.recv`**:

When `msg.epoch ≠ States.epochOf self` no payload handler is called, so the call is total:

• `msg.epoch < epochOf self`: the message is from an earlier epoch — the result is
  `Ok { key := none, state := self }` (`recv_of_lt`).
• `msg.epoch > epochOf self`, `self = Ct2Sampled st` and `msg.epoch = st.uc.epoch + 1`: the
  party moves to the next epoch — the result is `Ok { key := none, state := KeysUnsampled ku }`
  with `ku.uc.epoch = msg.epoch` and `ku.uc.auth = st.uc.auth` (`recv_Ct2Sampled_next_epoch`).
• `msg.epoch > epochOf self` otherwise: the result is `Err (EpochOutOfRange msg.epoch)`
  (`recv_of_gt`).

The result satisfies `recvPost self msg`; the same-epoch clause holds vacuously.

**Source**: spqr/src/v1/chunked/states.rs (lines 275:4-533:5)
-/
theorem recv_spec_of_ne (self : States) (msg : Message) (h : msg.epoch ≠ self.epochOf) :
    recv self msg ⦃ (result : core.result.Result Recv Error) => recvPost self msg result ⦄ := by
  have hne : msg.epoch.val ≠ self.epochOf.val := fun hv => h (UScalar.eq_of_val_eq hv)
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · rw [recv_of_lt self msg hlt, WP.spec_ok]
    exact ⟨fun _ => rfl, fun heq => absurd heq h, fun hgt => absurd hgt (by omega)⟩
  · by_cases hnext : ∃ st, self = .Ct2Sampled st ∧ msg.epoch.val = st.uc.epoch.val + 1
    · obtain ⟨st, rfl, hn⟩ := hnext
      rw [recv_Ct2Sampled_next_epoch st msg hn, WP.spec_ok]
      refine ⟨fun hlt => absurd hlt (by omega), fun heq => absurd heq h, fun _ => ?_⟩
      simp only [hn, ↓reduceIte]
    · have hnext' : ∀ st, self = .Ct2Sampled st → msg.epoch.val ≠ st.uc.epoch.val + 1 :=
        fun st hs hn => hnext ⟨st, hs, hn⟩
      rw [recv_of_gt self msg hgt hnext', WP.spec_ok]
      refine ⟨fun hlt => absurd hlt (by omega), fun heq => absurd heq h, fun _ => ?_⟩
      cases self with
      | Ct2Sampled st => simp only [hnext' st rfl, ↓reduceIte]
      | _ => rfl

/-! ## Spec theorem -/

/-- **Spec theorem for `spqr.v1.chunked.states.States.recv`**:

• Takes the current chunked state `self : States` and the received message `msg : Message`
  (epoch `msg.epoch`, payload `msg.payload`).
• Every arm first evaluates `state.epoch()` — the epoch of the unchunked payload,
  `States.epochOf self` — and compares it with `msg.epoch` through `OrdU64.cmp`.
• `Ordering::Less`: returns `Ok { key := none, state := self }` without reading the payload.
• `Ordering::Greater`: returns `Err (EpochOutOfRange msg.epoch)`, except in `Ct2Sampled st`
  with `msg.epoch = st.uc.epoch + 1`, where it returns the `KeysUnsampled` state produced by
  `Ct2Sampled::recv_next_epoch` — epoch `msg.epoch`, authenticator of `st` — and no key.
• `Ordering::Equal`: dispatches on the payload.  The expected pairs and their handlers are
    - `KeysSampled` / `Ct1`: `KeysSampled::recv_ct1_chunk` → `HeaderSent`;
    - `HeaderSent` / `Ct1`: `HeaderSent::recv_ct1_chunk` → `HeaderSent` or `Ct1Received`;
    - `Ct1Received` / `Ct2`: `Ct1Received::recv_ct2_chunk` → `EkSentCt1Received`;
    - `EkSentCt1Received` / `Ct2`: `EkSentCt1Received::recv_ct2_chunk?` → `EkSentCt1Received`,
      or `NoHeaderReceived` together with the epoch secret as `key`;
    - `NoHeaderReceived` / `Hdr`: `NoHeaderReceived::recv_hdr_chunk?` → `NoHeaderReceived` or
      `HeaderReceived`;
    - `Ct1Sampled` / `Ek`, `EkCt1Ack`: `Ct1Sampled::recv_ek_chunk? (ack := false / true)` →
      `Ct1Sampled`, `Ct1Acknowledged`, `EkReceivedCt1Sampled` or `Ct2Sampled`;
    - `EkReceivedCt1Sampled` / `EkCt1Ack`, `Ct1Ack true`: `recv_ct1_ack` → `Ct2Sampled`;
    - `Ct1Acknowledged` / `Ek`, `EkCt1Ack`: `Ct1Acknowledged::recv_ek_chunk?` →
      `Ct1Acknowledged` or `Ct2Sampled`.
  An `Err` propagated by `?` is returned unchanged; any other state / payload pair returns
  `Ok { key := none, state := self }`.  Only the `EkSentCt1Received` completion emits a key.

The result satisfies `recvPost self msg result`: on the two epoch-mismatch outcomes the exact
result as above, and on the same-epoch outcome `recvEqPost self msg result`, which pins the
result to the value returned by the handler of the matched pair.

The premise `hpre : recvPre self msg` collects, for the same-epoch case only, the
preconditions of the handler the dispatcher calls (`recvHandlerPre`): the exact hypotheses
of the handlers' `*_spec_concrete` theorems — decoder validity, buffer lengths, scalar
bounds, the values of the opaque ML-KEM size constants.  They are what a bare `States` value
does not establish; under them every handler returns (`recv_eq_ok_of_eq`) and the result is
`recvEqPost` (`recv_spec_of_eq`).  The epoch-mismatch paths are total and need nothing
(`recv_spec_of_ne`, `recvPre_of_ne`).

The postcondition pins the result to the handler's return value and deliberately states no
property of the successor state itself.  A caller needing facts about `result.state` (epoch,
authenticator, decoder well-formedness, …) obtains the equation `handler … = ok r` from
`recvEqPost` and applies the handler's own spec theorem to it; `key_some_of_recvPost` isolates
the single key-emitting path.

**Source**: spqr/src/v1/chunked/states.rs (lines 275:4-533:5)
-/
@[step]
theorem recv_spec (self : States) (msg : Message) (hpre : recvPre self msg) :
    recv self msg ⦃ (result : core.result.Result Recv Error) => recvPost self msg result ⦄ := by
  by_cases h : msg.epoch = self.epochOf
  · refine WP.spec_mono (recv_spec_of_eq self msg h (hpre h)) (fun r hr => ?_)
    exact ⟨fun hlt => absurd hlt (by rw [h]; exact lt_irrefl _), fun _ => hr,
      fun hgt => absurd hgt (by rw [h]; exact lt_irrefl _)⟩
  · exact recv_spec_of_ne self msg h

end spqr.v1.chunked.states.States
