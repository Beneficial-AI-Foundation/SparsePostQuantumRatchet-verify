/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
module

public import SrcTranslated.Funs
import Spqr.Auxiliary.Aeneas.SpecImpExists
public import Spqr.Specs.Lib.ChainFrom
public import Spqr.Specs.Lib.ChainFromVersionNegotiation
import Spqr.Specs.Lib.InitInner
public import Spqr.Specs.Lib.Send
import Spqr.Specs.Proto.PqRatchet.Direction.TryFrom
/-!
# Spec theorem for `spqr::recv`

`recv` parses the message preamble and decodes the serialised state, negotiates the protocol
version, then receives the message with the version-1 state machine and the key chain.

Version negotiation, the part of `recv` that touches nothing cryptographic, is the pure
function `negotiate`. Let `v` be the peer's version byte. A state whose PQ ratchet is disabled
(no inner state, version 0) accepts everything and does nothing, except that `v` below the
minimum version of a present `VersionNegotiation` record is `Err MinimumVersion`. A state with
an inner state (version 1) and a negotiation record rejects `v` below its minimum version the
same way, negotiates down to version 0 for `v = 0`, receives the message for `v = 1`, and for
`v > 1` serves a key from chain epoch 0 and keeps the record for a later negotiation. Once the
record is gone, `v = 0` is `Err MinimumVersion`, `v > 1` is `Err VersionMismatch`, and only
`v = 1` receives the message.

Negotiating down to version 0 requires the record's direction to parse (`Err StateDecode`
otherwise) and disables the ratchet: the result is the empty state. The source still rebuilds
the key chain on that path, so a failure of that rebuild is the only observable effect, and the
postcondition keeps the rebuild for that reason.

The rest of `recv` is the program in the postcondition of `recv_spec`. Each step calls the
model of its callee where one exists (`chainFrom`, `parseDirection`) and the extracted
function otherwise (`States::from_pb`, `States::recv`, `States::into_pb`, the chain
operations, `Message::deserialize`, the prost encoder). A step whose source call carries `?`
is followed by `orErr`, which returns its `Err`; every other step can only panic.

`recv_spec` is a total triple, so it needs a no-panic precondition. `States::recv` and the
chain operations can panic on some states and no state invariant is specified yet, so the
precondition is the assumption itself: the call does not panic. The proof shows that `recv` is
the postcondition program on every input, panics included, and the precondition then turns
that equation into the triple.

**Source**: spqr/src/lib.rs (lines 355:0-455:1)
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr

/-- Result of `recv` while the PQ ratchet is disabled: the empty state and no key. -/
def recvDisabled : Recv := { state := alloc.vec.Vec.new U8, key := none }

/-- Outcome of a successful version negotiation in `recv`; the failures are the `Err` values of
`negotiate`. -/
inductive Negotiation where
  /-- The PQ ratchet is disabled: nothing to receive. -/
  | disabled
  /-- The peer is at version 0: negotiate down with the record `vn`, which disables the ratchet. -/
  | downgrade (vn : proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
  /-- Same version on both sides: receive the message with the inner state `pb`. -/
  | proceed (pb : proto.pq_ratchet.V1State)
  /-- The peer is at a higher version: serve a key from chain epoch 0 and keep negotiating. -/
  | ahead

/-- Version negotiation in `recv`, from the decoded state and the peer's version byte. A state
is at version 1 with an inner state and at version 0 without; the minimum version of a
negotiation record is an `i32` cast to `u8` as in the source, so values outside `0..255`
wrap. A version below the minimum is `Err MinimumVersion` (the minimum is 1 once the record is
gone), a version above 1 once the record is gone is `Err VersionMismatch`, and a downgrade
whose record has no valid direction is `Err StateDecode`. -/
def negotiate (st : proto.pq_ratchet.PqRatchetState) (version : U8) :
    core.result.Result Negotiation Error :=
  match st.inner, st.version_negotiation with
  | none, some vn =>
    if version < IScalar.hcast .U8 vn.min_version then .Err Error.MinimumVersion
    else .Ok .disabled
  | none, none => .Ok .disabled
  | some (.V1 pb), some vn =>
    if version < IScalar.hcast .U8 vn.min_version then .Err Error.MinimumVersion
    else if version < 1#u8 then
      match parseDirection vn with
      | none => .Err Error.StateDecode
      | some _ => .Ok (.downgrade vn)
    else if version = 1#u8 then .Ok (.proceed pb)
    else .Ok .ahead
  | some (.V1 pb), none =>
    if version < 1#u8 then .Err Error.MinimumVersion
    else if version = 1#u8 then .Ok (.proceed pb)
    else .Err Error.VersionMismatch

/-- Discharge a `?`-propagated error branch. -/
local macro "close_err" : tactic =>
  `(tactic| simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from, orErr])

/-- `Direction::try_from` on the direction field of a negotiation record, in terms of
`parseDirection`. -/
private theorem try_from_direction (vn : proto.pq_ratchet.pq_ratchet_state.VersionNegotiation) :
    proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from
      vn.direction =
    ok (match parseDirection vn with
      | none => core.result.Result.Err vn.direction
      | some d => core.result.Result.Ok d) := by
  obtain ⟨r, h, hr⟩ := WP.spec_imp_exists
    (proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from_spec
      vn.direction)
  rw [h, hr]
  unfold parseDirection
  split <;> simp_all

/-- Receiving at the same version: the extracted block from the payload deserialisation on
equals the postcondition program's. -/
private theorem recv_v1_eq (stored : Option proto.pq_ratchet.Chain)
    (vn : Option proto.pq_ratchet.pq_ratchet_state.VersionNegotiation) (mp : MsgPreamble)
    (pb : proto.pq_ratchet.V1State) :
    (do
      let r2 ← v1.chunked.states.serialize.Message.deserialize mp.epoch mp.remaining
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 => do
        let r3 ← v1.chunked.states.serialize.States.from_pb pb
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val2 => do
          let r4 ← v1.chunked.states.States.recv val2 val1
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val3 => do
            let msg_key_epoch ← mp.epoch - 1#u64
            let o2 ← core.option.Option.as_ref vn
            let r5 ← chain_from stored o2
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val4 => do
              let ratchet_chain ← match val3.key with
                | none => ok val4
                | some epoch_secret => chain.Chain.add_epoch val4 epoch_secret
              let (r6, ratchet_chain1) ←
                chain.Chain.recv_key ratchet_chain msg_key_epoch mp.index
              let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue val5 => do
                let vs ← v1.chunked.states.serialize.States.into_pb val3.state
                let c ← chain.Chain.into_pb ratchet_chain1
                let v1 ← encode_state_pb
                  { version_negotiation := none, chain := some c,
                    inner := some (proto.pq_ratchet.pq_ratchet_state.Inner.V1 vs) }
                let b ← alloc.vec.Vec.is_empty Global val5
                if b = true then ok (core.result.Result.Ok { state := v1, key := none })
                else ok (core.result.Result.Ok { state := v1, key := some val5 })
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Recv
                  (core.convert.FromSame Error) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Recv
                (core.convert.FromSame Error) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Recv
              (core.convert.FromSame Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Recv
            (core.convert.FromSame Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Recv
          (core.convert.FromSame Error) residual :
      Result (core.result.Result Recv Error)) =
    (do
      let m ← v1.chunked.states.serialize.Message.deserialize mp.epoch mp.remaining
      orErr m fun m => do
      let s ← v1.chunked.states.serialize.States.from_pb pb
      orErr s fun s => do
      let r ← v1.chunked.states.States.recv s m
      orErr r fun r => do
      let epoch ← mp.epoch - 1#u64
      let c ← chainFrom stored vn
      orErr c fun c => do
      let c ← match r.key with
        | none => ok c
        | some es => chain.Chain.add_epoch c es
      let (key, c) ← chain.Chain.recv_key c epoch mp.index
      orErr key fun key => do
      let vs ← v1.chunked.states.serialize.States.into_pb r.state
      let cpb ← chain.Chain.into_pb c
      let bytes ← encode_state_pb
        { version_negotiation := none, chain := some cpb, inner := some (.V1 vs) }
      ok (.Ok { state := bytes, key := if key.val = [] then none else some key })) := by
  simp only [core.result.Result.Insts.CoreOpsTry.branch, core.option.Option.as_ref, bind_ok,
    orErr]
  congr 1
  funext r2
  cases r2 with
  | Err e => close_err
  | Ok m =>
    simp only [bind_ok]
    congr 1
    funext r3
    cases r3 with
    | Err e => close_err
    | Ok s =>
      simp only [bind_ok]
      congr 1
      funext r4
      cases r4 with
      | Err e => close_err
      | Ok r =>
        simp only [bind_ok]
        congr 1
        funext epoch
        obtain ⟨r5, h5, hr5⟩ := WP.spec_imp_exists (chain_from_spec stored vn)
        rw [h5, hr5]
        cases r5 with
        | Err e => close_err
        | Ok c =>
          simp only [bind_ok]
          rcases r with ⟨key, st⟩
          -- The chain update is `ok c` or `add_epoch c es`; from the chain `rc` on, the arms agree.
          cases key
          case' none => simp only [bind_ok]
          case' some es =>
            congr 1
            funext rc
          all_goals
            congr 1
            funext p
            rcases p with ⟨r6, c1⟩
            simp only [uncurry_apply_pair]
            cases r6 with
            | Err e => close_err
            | Ok key =>
              simp only [bind_ok, alloc.vec.Vec.is_empty]
              congr 1
              funext vs
              congr 1
              funext cpb
              congr 1
              funext bytes
              by_cases hk : key.val = []
              · simp [hk]
              · simp [hk]

/-- **Spec theorem for `spqr::recv`**
• Precondition `h_no_panic`: the call does not panic. Nothing specified so far implies it,
  since `States::recv` and the chain operations can panic on some states.
• The result is the value of the program in the postcondition. In particular: a message that
  does not parse is `Err MsgDecode` and a state that does not decode is `Err StateDecode`, both
  before any negotiation; version negotiation is `negotiate`, one of its four outcomes or
  `Err MinimumVersion`, `Err VersionMismatch` or `Err StateDecode` before anything else
  happens; a peer ahead is served the chain key for epoch 0 at the message index, and the state
  keeps its negotiation record; at the same version the payload is deserialised, the state
  machine steps, any new epoch secret enters the chain, the message key is the chain key for
  `epoch - 1` at the message index, and the state is re-encoded with the negotiation record
  cleared.

**Source**: spqr/src/lib.rs (lines 355:0-455:1) -/
@[step]
theorem recv_spec (state msg : alloc.vec.Vec U8)
    (h_no_panic : recv state msg ⦃ _ => True ⦄) :
    recv state msg ⦃ (result : core.result.Result Recv Error) =>
      (do
        let mp ← msg_preamble msg
        orErr mp fun mp => do
        let st ← decode_state state
        orErr st fun st =>
        orErr (negotiate st mp.version) fun
        | .disabled => ok (.Ok recvDisabled)
        | .downgrade vn => do
          let c ← chainFrom st.chain (some vn)
          orErr c fun c => do
          let _ ← chain.Chain.into_pb c
          ok (.Ok recvDisabled)
        | .ahead => do
          let c ← chainFrom st.chain st.version_negotiation
          orErr c fun c => do
          let (key, c) ← chain.Chain.recv_key c 0#u64 mp.index
          orErr key fun key => do
          let cpb ← chain.Chain.into_pb c
          let bytes ← encode_state_pb { st with chain := some cpb }
          ok (.Ok { state := bytes, key := some key })
        | .proceed pb => do
          let m ← v1.chunked.states.serialize.Message.deserialize mp.epoch mp.remaining
          orErr m fun m => do
          let s ← v1.chunked.states.serialize.States.from_pb pb
          orErr s fun s => do
          let r ← v1.chunked.states.States.recv s m
          orErr r fun r => do
          let epoch ← mp.epoch - 1#u64
          let c ← chainFrom st.chain st.version_negotiation
          orErr c fun c => do
          let c ← match r.key with
            | none => ok c
            | some es => chain.Chain.add_epoch c es
          let (key, c) ← chain.Chain.recv_key c epoch mp.index
          orErr key fun key => do
          let vs ← v1.chunked.states.serialize.States.into_pb r.state
          let cpb ← chain.Chain.into_pb c
          let bytes ← encode_state_pb
            { version_negotiation := none, chain := some cpb, inner := some (.V1 vs) }
          ok (.Ok { state := bytes, key := if key.val = [] then none else some key }) :
        Result (core.result.Result Recv Error)) = ok result ⦄ := by
  obtain ⟨v, hv, -⟩ := WP.spec_imp_exists h_no_panic
  rw [hv, WP.spec_ok, ← hv]
  symm
  unfold recv
  congr 1
  funext r
  cases r with
  | Err e => close_err
  | Ok mp =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, orErr]
    congr 1
    funext r1
    cases r1 with
    | Err e => close_err
    | Ok st =>
      rcases st with ⟨vn, chain, inner⟩
      simp only [bind_ok, state_version]
      cases inner with
      | none =>
        simp only [bind_ok, lift, negotiate,
          show IScalar.hcast .U8 (read_discriminant proto.pq_ratchet.Version.V0) = 0#u8 from rfl]
        cases vn with
        | none =>
          simp only [bind_ok, Std.bind_assoc]
          change Aeneas.Std.bind (ok true) _ = _
          simp only [bind_ok, uncurry_apply_pair, ite_true, ite_self, recvDisabled]
          rw [ite_eq_right (show ¬ mp.version < 0#u8 by scalar_tac)]
        | some vn1 =>
          simp only [bind_ok, uncurry_apply_pair]
          by_cases h1 : mp.version < IScalar.hcast .U8 vn1.min_version
          · simp only [ite_eq_left h1]
          · simp only [ite_eq_right h1, ite_true, ite_self, recvDisabled]
      | some i =>
        rcases i with ⟨pb⟩
        simp only [bind_ok, lift, negotiate,
          show IScalar.hcast .U8 (read_discriminant proto.pq_ratchet.Version.V1) = 1#u8 from rfl]
        cases vn with
        | none =>
          simp only [bind_ok, Std.bind_assoc]
          change Aeneas.Std.bind (ok false) _ = _
          simp only [bind_ok, uncurry_apply_pair]
          by_cases h1 : mp.version < 1#u8
          · simp only [ite_eq_left h1]
          · by_cases h2 : mp.version = 1#u8
            · simp only [ite_eq_right h1, ite_eq_left h2]
              simp only [h2, bne_self_eq_false, Bool.false_eq_true, ite_false,
                ite_eq_right (show ¬ (1#u8 : U8) = 0#u8 by scalar_tac),
                show core.cmp.impls.OrdU8.cmp 1#u8 1#u8 = Ordering.eq from rfl]
              exact recv_v1_eq chain none mp pb
            · simp only [ite_eq_right h1, ite_eq_right h2, ite_eq_left (bne_iff_ne.mpr h2),
                Bool.false_eq_true, ite_false]
        | some vn1 =>
          simp only [bind_ok, uncurry_apply_pair]
          by_cases h1 : mp.version < IScalar.hcast .U8 vn1.min_version
          · simp only [ite_eq_left h1]
          · simp only [ite_eq_right h1, ite_true,
              ite_eq_right (show ¬ (1#u8 : U8) = 0#u8 by scalar_tac)]
            by_cases h2 : mp.version < 1#u8
            · -- Downgrade to version 0.
              simp only [ite_eq_left h2,
                ite_eq_left (bne_iff_ne.mpr (show mp.version ≠ 1#u8 by scalar_tac)),
                show core.cmp.impls.OrdU8.cmp mp.version 1#u8 = Ordering.lt by
                  simp only [core.cmp.impls.OrdU8.cmp, Nat.compare_eq_lt]; scalar_tac,
                bind_ok, (massert_ok _).mpr (show (1#u8 : U8) > 0#u8 by scalar_tac), massert_True,
                core.option.Option.expect, Result.ofOption, core.result.Result.expect,
                try_from_direction vn1]
              simp only [show mp.version = 0#u8 by scalar_tac,
                show proto.pq_ratchet.Version.Insts.CoreConvertTryFromU8String.try_from 0#u8 =
                  ok (core.result.Result.Ok proto.pq_ratchet.Version.V0) from rfl, bind_ok]
              cases hd : parseDirection vn1 with
              | none =>
                simp only [bind_ok, core.result.Result.map_err,
                  recv.closure.Insts.CoreOpsFunctionFnOnceTupleUnknownEnumValueError.call_once]
                close_err
              | some d =>
                simp only [bind_ok, core.result.Result.map_err, init_inner]
                obtain ⟨r5, h5, hr5⟩ := WP.spec_imp_exists (chain_from_spec chain (some vn1))
                rw [h5, hr5]
                cases r5 with
                | Err e => close_err
                | Ok c =>
                  simp only [bind_ok]
                  congr 1
            · by_cases h3 : mp.version = 1#u8
              · -- Same version on both sides.
                simp only [ite_eq_right h2, ite_eq_left h3]
                simp only [h3, bne_self_eq_false, Bool.false_eq_true, ite_false,
                  show core.cmp.impls.OrdU8.cmp 1#u8 1#u8 = Ordering.eq from rfl]
                exact recv_v1_eq chain (some vn1) mp pb
              · -- The peer is ahead.
                simp only [ite_eq_right h2, ite_eq_right h3, ite_eq_left (bne_iff_ne.mpr h3),
                  show core.cmp.impls.OrdU8.cmp mp.version 1#u8 = Ordering.gt by
                    simp only [core.cmp.impls.OrdU8.cmp, Nat.compare_eq_gt]; scalar_tac,
                  bind_ok, core.option.Option.as_ref, recv.ZERO_EPOCH]
                obtain ⟨r4, h4, hr4⟩ := WP.spec_imp_exists (chain_from_spec chain (some vn1))
                rw [h4, hr4]
                cases r4 with
                | Err e => close_err
                | Ok c =>
                  simp only [bind_ok]
                  congr 1
                  funext p
                  rcases p with ⟨r3, c2⟩
                  simp only [uncurry_apply_pair]
                  cases r3 with
                  | Err e => close_err
                  | Ok key => simp only [bind_ok]

end spqr
