/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
module

public import SrcTranslated.Funs
import Spqr.Auxiliary.Aeneas.SpecImpExists
public import Spqr.Specs.Lib.ChainFromVersionNegotiation
import Spqr.Specs.Chain.Chain.FromPb
public import Spqr.Specs.Chain.Chain.FunctionalModels
import Spqr.Specs.V1.Chunked.States.Serialize.Message.Serialize
/-!
# Spec theorem for `spqr::send`

`send` decodes the serialised state and, while the PQ ratchet is disabled, returns the empty
state, the empty message and no key. Otherwise it steps the version-1 state machine with the
RNG, picks the key chain with `chainSource`, draws the send key for the previous epoch,
serialises the message with the chain index, and re-encodes the state with the negotiation
record unchanged. The key is attached only when it is non-empty.

`chainSource`, the part of `send` that touches nothing cryptographic, is pure. A stored chain
is deserialised; without one, a `VersionNegotiation` record whose minimum version is above 0
builds a fresh chain, a record whose minimum version is not above 0 means sending without a
chain, and no record is `Err ChainNotAvailable`. Sending without a chain asserts that the state
machine produced no epoch secret: the source only assumes this (`hax_lib::assume!`), nothing
specified so far implies it, and the postcondition keeps the assertion. The source's two
assertions on the serialised message always hold by `Message.serialize_spec` and are left out.

The rest of `send` is the program in the postcondition of `send_spec`: the RNG is threaded
until the state machine has stepped, and from there on the program runs without it. Each step
calls the model of its callee where one exists (`Chain.FunctionalModels.fromPb`,
`chainFromVersionNegotiation`) and the extracted function otherwise (`States::from_pb`,
`States::send`, `States::into_pb`, the chain operations, `Message::serialize`, the prost
encoder). A step whose source call carries `?` is followed by `orErr` (`orErrRng` while the
RNG is threaded), which returns its `Err`; every other step can only panic.

`send_spec` is a total triple, so it needs a no-panic precondition. `States::send` and the
chain operations can panic on some states and no state invariant is specified yet, so the
precondition is the assumption itself: the call does not panic. The proof shows that `send` is
the postcondition program on every input, panics included, and the precondition then turns
that equation into the triple.

**Source**: spqr/src/lib.rs (lines 264:0-326:1)
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr

/-- Rust's `?` on a `Result` value: an `Err` is returned as it is, an `Ok` value is passed on
to `k`. -/
def orErr {α β : Type} (r : core.result.Result α Error)
    (k : α → Result (core.result.Result β Error)) : Result (core.result.Result β Error) :=
  match r with
  | .Err e => ok (.Err e)
  | .Ok a => k a

/-- `orErr` for a computation that also returns the RNG: an `Err` is returned together with
the RNG `rng` as it stands at that point. -/
def orErrRng {α β R : Type} (r : core.result.Result α Error) (rng : R)
    (k : α → Result (core.result.Result β Error × R)) :
    Result (core.result.Result β Error × R) :=
  match r with
  | .Err e => ok (.Err e, rng)
  | .Ok a => k a

/-- Result of `send` while the PQ ratchet is disabled: the empty state, the empty message and
no key. -/
def sendDisabled : Send :=
  { state := alloc.vec.Vec.new U8, msg := alloc.vec.Vec.new U8, key := none }

/-- Where `send` takes its key chain from. -/
inductive ChainSource where
  /-- A chain is stored in the state. -/
  | stored (pb : proto.pq_ratchet.Chain)
  /-- No chain is stored; version negotiation with a minimum version above 0 builds one. -/
  | negotiated (vn : proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
  /-- No chain is stored and the minimum version is not above 0: send without a chain. -/
  | absent
  /-- No chain is stored and no negotiation record exists: `Err ChainNotAvailable`. -/
  | unavailable

/-- The key chain `send` uses, from the decoded state. -/
def chainSource (st : proto.pq_ratchet.PqRatchetState) : ChainSource :=
  match st.chain, st.version_negotiation with
  | some pb, _ => .stored pb
  | none, some vn => if vn.min_version > 0#i32 then .negotiated vn else .absent
  | none, none => .unavailable

/-- Discharge a `?`-propagated error branch. -/
local macro "close_err" : tactic =>
  `(tactic| simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from, orErr, orErrRng])

/-- The extracted finish of `send`, from the message serialisation on, equals the postcondition
program's: the two source assertions on the serialised message hold by
`Message.serialize_spec`, and the key is attached exactly when it is non-empty. -/
private theorem send_finish_eq {R : Type}
    (vn : Option proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (msg : v1.chunked.states.Message) (st : v1.chunked.states.States) (index : U32)
    (msgKey : alloc.vec.Vec U8) (chainPb : Option proto.pq_ratchet.Chain) (rng1 : R) :
    (do
      let msg ← v1.chunked.states.serialize.Message.serialize msg index
      let b1 ← alloc.vec.Vec.is_empty Global msg
      massert (¬ b1 = true)
      let left_val ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8) msg 0#usize
      let right_val ← core.convert.IntoFrom.into U8.Insts.CoreConvertFromVersion
        proto.pq_ratchet.Version.V1
      massert (left_val = right_val)
      let vs ← v1.chunked.states.serialize.States.into_pb st
      let v ← encode_state_pb
        { version_negotiation := vn, chain := chainPb,
          inner := some (proto.pq_ratchet.pq_ratchet_state.Inner.V1 vs) }
      let b2 ← alloc.vec.Vec.is_empty Global msgKey
      if b2 = true then ok (core.result.Result.Ok { state := v, msg := msg, key := none }, rng1)
      else ok (core.result.Result.Ok { state := v, msg := msg, key := some msgKey }, rng1) :
      Result (core.result.Result Send Error × R)) =
    (do
      let m ← v1.chunked.states.serialize.Message.serialize msg index
      let vs ← v1.chunked.states.serialize.States.into_pb st
      let bytes ← encode_state_pb
        { version_negotiation := vn, chain := chainPb,
          inner := some (proto.pq_ratchet.pq_ratchet_state.Inner.V1 vs) }
      ok (core.result.Result.Ok
        { state := bytes, msg := m,
          key := if msgKey.val = [] then none else some msgKey }, rng1)) := by
  obtain ⟨m, hm, hb⟩ :=
    WP.spec_imp_exists (v1.chunked.states.serialize.Message.serialize_spec msg index)
  rw [hm]
  obtain ⟨b, bs, hmv⟩ : ∃ b bs, m.val = b :: bs := by
    rcases h : m.val with _ | ⟨b, bs⟩
    · rw [h] at hb
      simp only [List.map_nil, v1.chunked.states.serialize.messageBytes, reduceCtorEq] at hb
    · exact ⟨b, bs, rfl⟩
  have hb1 : b = 1#u8 := by
    rw [hmv] at hb
    simp only [List.map_cons, v1.chunked.states.serialize.messageBytes, List.cons.injEq] at hb
    exact UScalar.eq_of_val_eq (by simp [hb.1])
  simp only [bind_ok, alloc.vec.Vec.is_empty, alloc.vec.Vec.index_slice_index]
  rw [show massert (¬ m.val.isEmpty = true) = ok () by simp [massert, hmv],
    show alloc.vec.Vec.index_usize m 0#usize = ok b by simp [alloc.vec.Vec.index_usize, hmv],
    show core.convert.IntoFrom.into U8.Insts.CoreConvertFromVersion
      proto.pq_ratchet.Version.V1 = ok 1#u8 by
      simp [core.convert.IntoFrom.into, U8.Insts.CoreConvertFromVersion.from]]
  simp only [bind_ok]
  rw [show massert (b = 1#u8) = ok () by simp [massert, hb1]]
  simp only [bind_ok]
  congr 1
  funext vs
  congr 1
  funext v
  by_cases hk : msgKey.val = []
  · simp [hk]
  · simp [hk]

/-- The extracted continuation of `send` once a key chain `c` is in hand equals the
postcondition program's: the chain step followed by the finish. -/
private theorem send_after_chain {R : Type}
    (vn : Option proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (out : v1.chunked.states.Send) (c : chain.Chain) (rng1 : R) :
    (do
      let ratchet_chain ← match out.key with
        | none => ok c
        | some epoch_secret => chain.Chain.add_epoch c epoch_secret
      let i3 ← out.msg.epoch - 1#u64
      let (r4, ratchet_chain1) ← chain.Chain.send_key ratchet_chain i3
      let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
      match cf4 with
      | core.ops.control_flow.ControlFlow.Continue val4 =>
        let (index, msg_key) := val4
        do
        let c ← chain.Chain.into_pb ratchet_chain1
        let msg ← v1.chunked.states.serialize.Message.serialize out.msg index
        let b1 ← alloc.vec.Vec.is_empty Global msg
        massert (¬ b1 = true)
        let left_val ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8) msg 0#usize
        let right_val ← core.convert.IntoFrom.into U8.Insts.CoreConvertFromVersion
          proto.pq_ratchet.Version.V1
        massert (left_val = right_val)
        let vs ← v1.chunked.states.serialize.States.into_pb out.state
        let v ← encode_state_pb
          { version_negotiation := vn, chain := some c,
            inner := some (proto.pq_ratchet.pq_ratchet_state.Inner.V1 vs) }
        let b2 ← alloc.vec.Vec.is_empty Global msg_key
        if b2 = true then ok (core.result.Result.Ok { state := v, msg := msg, key := none }, rng1)
        else ok (core.result.Result.Ok { state := v, msg := msg, key := some msg_key }, rng1)
      | core.ops.control_flow.ControlFlow.Break residual => do
        let r5 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Send
          (core.convert.FromSame Error) residual
        ok (r5, rng1) :
      Result (core.result.Result Send Error × R)) =
    (do
      let keyed : core.result.Result (U32 × alloc.vec.Vec U8 × Option proto.pq_ratchet.Chain)
          Error ← (do
        let c ← match out.key with
          | none => ok c
          | some es => chain.Chain.add_epoch c es
        let epoch ← out.msg.epoch - 1#u64
        let (r, c) ← chain.Chain.send_key c epoch
        orErr r fun (index, msgKey) => do
        let cpb ← chain.Chain.into_pb c
        ok (.Ok (index, msgKey, some cpb)))
      orErrRng keyed rng1 fun (index, msgKey, chainPb) => do
      let msg ← v1.chunked.states.serialize.Message.serialize out.msg index
      let vs ← v1.chunked.states.serialize.States.into_pb out.state
      let bytes ← encode_state_pb
        { version_negotiation := vn, chain := chainPb, inner := some (.V1 vs) }
      ok (core.result.Result.Ok
        { state := bytes, msg := msg, key := if msgKey.val = [] then none else some msgKey },
        rng1)) := by
  rcases out with ⟨msg, key, st⟩
  simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_assoc]
  -- The chain update is `ok c` or `add_epoch c es`; from the chain `rc` on, the arms agree.
  cases key
  case' none => simp only [bind_ok]
  case' some es =>
    congr 1
    funext rc
  all_goals
    congr 1
    funext i3
    congr 1
    funext p
    rcases p with ⟨r4, c1⟩
    simp only [uncurry_apply_pair]
    cases r4 with
    | Err e => close_err
    | Ok v =>
      rcases v with ⟨index, msg_key⟩
      simp only [uncurry_apply_pair, bind_ok, Std.bind_assoc, orErr, orErrRng]
      congr 1
      funext cpb
      exact send_finish_eq vn msg st index msg_key (some cpb) rng1

/-- **Spec theorem for `spqr::send`**
• Precondition `h_no_panic`: the call does not panic. Nothing specified so far implies it,
  since `States::send` and the chain operations can panic on some states.
• The result is the value of the program in the postcondition. In particular: a state that does
  not decode is `Err StateDecode`; a disabled ratchet sends the empty state and the empty
  message with no key; otherwise the state machine steps first, with the RNG, and the key chain
  is `chainSource`; with a chain, any new epoch secret enters it, the message key is its send
  key for `epoch - 1`, and the message carries that key's index; without one the index is 0 and
  there is no key; the state is re-encoded with the new inner state and chain and the
  negotiation record unchanged.
• An error before the state machine has stepped returns the RNG unchanged, a later one returns
  the stepped RNG.

**Source**: spqr/src/lib.rs (lines 264:0-326:1) -/
@[step]
theorem send_spec {R : Type} (rand_1rngRngInst : rand_1.rng.Rng R)
    (rand_core_1CryptoRngInst : rand_core_1.CryptoRng R) (state : alloc.vec.Vec U8) (rng : R)
    (h_no_panic : send rand_1rngRngInst rand_core_1CryptoRngInst state rng ⦃ _ => True ⦄) :
    send rand_1rngRngInst rand_core_1CryptoRngInst state rng ⦃ (result :
        core.result.Result Send Error × R) =>
      (do
        let dec ← decode_state state
        orErrRng dec rng fun st =>
        match st.inner with
        | none => ok (.Ok sendDisabled, rng)
        | some (.V1 pb) => do
        let decoded ← v1.chunked.states.serialize.States.from_pb pb
        orErrRng decoded rng fun s => do
        let (r, rng) ←
          v1.chunked.states.States.send rand_1rngRngInst rand_core_1CryptoRngInst s rng
        orErrRng r rng fun out => do
        let keyed : core.result.Result
            (U32 × alloc.vec.Vec U8 × Option proto.pq_ratchet.Chain) Error ←
          match chainSource st with
          | .stored cpb => orErr (chain.Chain.FunctionalModels.fromPb cpb) fun c => do
            let c ← match out.key with
              | none => ok c
              | some es => chain.Chain.add_epoch c es
            let epoch ← out.msg.epoch - 1#u64
            let (r, c) ← chain.Chain.send_key c epoch
            orErr r fun (index, msgKey) => do
            let cpb ← chain.Chain.into_pb c
            ok (.Ok (index, msgKey, some cpb))
          | .negotiated vn => do
            let c ← chainFromVersionNegotiation vn
            orErr c fun c => do
            let c ← match out.key with
              | none => ok c
              | some es => chain.Chain.add_epoch c es
            let epoch ← out.msg.epoch - 1#u64
            let (r, c) ← chain.Chain.send_key c epoch
            orErr r fun (index, msgKey) => do
            let cpb ← chain.Chain.into_pb c
            ok (.Ok (index, msgKey, some cpb))
          | .absent => do
            massert out.key.isNone
            ok (.Ok (0#u32, alloc.vec.Vec.new U8, none))
          | .unavailable => ok (.Err Error.ChainNotAvailable)
        orErrRng keyed rng fun (index, msgKey, chainPb) => do
        let msg ← v1.chunked.states.serialize.Message.serialize out.msg index
        let vs ← v1.chunked.states.serialize.States.into_pb out.state
        let bytes ← encode_state_pb { st with chain := chainPb, inner := some (.V1 vs) }
        ok (.Ok { state := bytes, msg := msg,
                  key := if msgKey.val = [] then none else some msgKey }, rng) :
        Result (core.result.Result Send Error × R)) = ok result ⦄ := by
  obtain ⟨v, hv, -⟩ := WP.spec_imp_exists h_no_panic
  rw [hv, WP.spec_ok, ← hv]
  symm
  unfold send
  congr 1
  funext dec
  cases dec with
  | Err e => close_err
  | Ok st =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, orErrRng]
    rcases st with ⟨vn, chain, inner⟩
    cases inner with
    | none => rfl
    | some i =>
      rcases i with ⟨pb⟩
      dsimp only
      congr 1
      funext decoded
      cases decoded with
      | Err e => close_err
      | Ok s =>
        simp only [bind_ok]
        congr 1
        funext p
        rcases p with ⟨r, rng1⟩
        simp only [uncurry_apply_pair]
        cases r with
        | Err e => close_err
        | Ok out =>
          cases chain with
          | none =>
            cases vn with
            | none => simp only [chainSource, core.option.Option.as_ref, bind_ok]
            | some vn1 =>
              simp only [bind_ok, chainSource, core.option.Option.as_ref]
              have h00 : (0#i32 + 0#i32 : Result I32) = ok 0#i32 := by
                obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists
                  (IScalar.add_spec (x := 0#i32) (y := 0#i32) (by scalar_tac) (by scalar_tac))
                rw [hz, show z = 0#i32 from IScalar.eq_of_val_eq (by simp [hzv])]
              rw [h00]
              simp only [bind_ok, lift, show IScalar.cast IScalarTy.I32 0#i32 = 0#i32 from rfl]
              by_cases hmin : vn1.min_version > 0#i32
              · simp only [decide_eq_true hmin, Bool.true_or, ite_eq_left hmin, Std.bind_assoc]
                rw [show massert True = ok () by simp [massert]]
                simp only [bind_ok]
                obtain ⟨r3, h3, hr3⟩ :=
                  WP.spec_imp_exists (chain_from_version_negotiation_spec vn1)
                rw [h3, hr3]
                cases r3 with
                | Err e => close_err
                | Ok c =>
                  simp only [bind_ok, orErr]
                  exact send_after_chain (some vn1) out c rng1
              · simp only [decide_eq_false hmin, Bool.false_or, ite_eq_right hmin, bind_ok,
                  Std.bind_assoc, core.option.Option.is_none]
                congr 1
                funext _
                exact send_finish_eq (some vn1) out.msg out.state 0#u32 (alloc.vec.Vec.new U8) none
                  rng1
          | some pb1 =>
            simp only [bind_ok, chainSource]
            obtain ⟨r3, h3, hr3⟩ := WP.spec_imp_exists (chain.Chain.from_pb_spec pb1)
            rw [h3, hr3]
            cases hf : chain.Chain.FunctionalModels.fromPb pb1 with
            | Err e => close_err
            | Ok c =>
              simp only [bind_ok, orErr]
              exact send_after_chain vn out c rng1

end spqr
