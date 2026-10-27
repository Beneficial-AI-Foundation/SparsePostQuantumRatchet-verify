/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Lib.StatePb
public import Spqr.Specs.Lib.ChainFromVersionNegotiation
public import Spqr.Specs.Chain.Chain.FunctionalModels
public import Spqr.Specs.Chain.Chain.Defs
public import Spqr.Specs.V1.Chunked.States.Serialize.Message.Serialize
import Spqr.Specs.Lib.DecodeState
import Spqr.Specs.Chain.Chain.FromPb
import Spqr.Specs.Chain.Chain.AddEpoch
import Spqr.Specs.Chain.Chain.SendKey
import Spqr.Specs.Chain.Chain.IntoPb
import Spqr.Auxiliary.Aeneas.SpecRefl
/-!
# Spec theorem for `spqr::send`

SPQR (the Sparse Post-Quantum Ratchet) supplies keys that protect a conversation between two
parties. A *key* is a secret byte string that is needed to encrypt or decrypt one message; a
*key exchange* is a protocol by which the two parties arrive at the same secret without an
eavesdropper learning it. SPQR keeps refreshing the keys by running a quantum-resistant key
exchange (ML-KEM) over and over. Its state only moves forward: a key already handed out cannot
be recomputed from a later state, hence "ratchet". Each party keeps a *state*, serialised via
Protocol Buffers (protobuf, a binary format), containing:

- `inner`: how far the current round of the key exchange has progressed. A round spans many
  messages, since each message carries only a small chunk of the data the round exchanges,
  so each party records which pieces it has sent and received, along with the round number
  and the key material produced so far. `None` means that the ratchet is disabled
  (version V0) and no exchange is running;
- `chain`: the *key chain*, which turns the key exchange's secrets into one key per message. It
  holds the key material of the recent *epochs* (numbered rounds of the protocol). Each
  completed exchange yields a fresh shared secret, the *epoch secret*. Mixing it into the chain
  opens a new epoch with a fresh *running secret* for each direction of traffic. Hashing a
  running secret produces two values: the next message key, and a new running secret that
  overwrites the old one. Hence old keys cannot be recomputed from the current state.
- `version_negotiation`: the lowest accepted protocol version (`min_version`) and the data
  needed to start a key chain.

`send` runs once per outgoing message. Given

- the party's serialised state and
- a random number generator, used by the key exchange,

it returns either an error or a `Send` value, consisting of

- the new serialised state,
- the *ratchet message* for the other party, which travels alongside the outgoing message and
  carries the next chunk, if any, of the current round of the key exchange, and
- the message key for the outgoing message, if there is one.

The function `send` thus

  1. decodes the input state, raw protobuf bytes, into a protobuf struct (`decode_state`). If
     it has no inner state (`inner` is `None`), `send` returns a `Send` with empty state, empty
     ratchet message and no key, and stops.
  2. converts the inner state to its working type (`States::from_pb`) and runs one step of the
     key exchange (`States::send`). This is the only step that uses the random number
     generator, when the round needs fresh randomness (an ML-KEM key pair or a ciphertext). It
     yields the new inner state, the ratchet message (the round number plus the next chunk of
     key exchange data, if the round has one to send) and, if a new epoch opens, its epoch
     secret.
  3. picks the key chain. If the input state stores one, it is converted to its working type
     (`Chain::from_pb`). Otherwise the version negotiation data decides: no data at all is an
     error (`ChainNotAvailable`); `min_version <= 0` (the lowest accepted version is still V0,
     so the conversation may yet be downgraded to V0, which has no ratchet, and no key is
     handed out) means no chain; any other value makes `send` try to build a fresh chain from
     the data (`chain_from_version_negotiation`), which can fail.
  4. derives the message key, the third output. With a chain, it first mixes in the epoch
     secret, if step 2 produced one (`Chain::add_epoch`), then takes the next key of chain
     epoch `msg.epoch - 1` and that key's position in the epoch, the *ratchet index*
     (`Chain::send_key`, which can fail), and converts the chain back to its protobuf struct
     (`Chain::into_pb`). Without a chain, the ratchet index is `0`, there is no key, and an
     `assert!` checks that step 2 produced no epoch secret.
  5. assembles the other two outputs. The ratchet message from step 2 is serialised together
     with the ratchet index from step 4. The new serialised state is the protobuf encoding of the
     new inner state from step 2 (converted back to its protobuf struct by `States::into_pb`), the
     new chain from step 4 if there is one, and the version negotiation data from step 1,
     unchanged.

**Note:** The spec theorem's input hypothesis `h_assumptions` (see `SendAssumptions`)
has not yet been justified. It simply assumes that the currently still unspecified callees
`States::from_pb`, `States::send` and `States::into_pb` do not panic, and it also assumes some
other facts needed by the proof: mostly consistency conditions that an invariant on the whole
ratchet state would supply. The theorem describes `send` relative to the three unspecified
callees: it fixes the result in terms of what they return. It should therefore be considered
provisional until the callees are specified and the necessary invariant exists; it will then
likely need further adjustments and improvements.

**Source**: spqr/src/lib.rs (lines 271:0-331:1)
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr

open v1.chunked.states
open chain.Chain.FunctionalModels (fromPb intoPb)

/-! ## What the spec theorem for `send` assumes -/

/-- Everything `send_spec` assumes. Each item is stated only for the intermediate values `send`
actually computes before reaching it (the decoded state, the result of `States::from_pb`, and so
on). On an input where `send` returns before that point, for instance because decoding fails, the
item holds trivially and asks nothing:

- (a) No panic in `States::from_pb`, `States::send` and `States::into_pb`, which have no
  specification yet. Once they are specified, each item follows from the preconditions of that
  specification: size bounds for `States::from_pb` and `States::into_pb` (all that their
  component specifications demand so far) and, for `States::send`, also well-formed encoder
  states, since its polynomial encoders can panic on point counts that `States::from_pb` accepts.
  The items stay here either way, so `send_spec` does not change.
- (b) The `assert!` of `send` (no epoch secret on the no-chain path), the positivity of the
  message epoch and the preconditions of `add_epoch_spec` and `send_key_spec` that `send` cannot
  establish. No callee specification supplies these facts; they need an invariant on the whole
  ratchet state. -/
def SendAssumptions {R : Type} (rngInst : rand_1.rng.Rng R) (cryptoInst : rand_core_1.CryptoRng R)
    (state : alloc.vec.Vec U8) (rng : R) : Prop :=
  ∀ st, decode_state state = ok (.Ok st) → ∀ pb, st.inner = some (.V1 pb) →
    serialize.States.from_pb pb ⦃ _ => True ⦄ ∧
    ∀ s, serialize.States.from_pb pb = ok (.Ok s) →
      States.send rngInst cryptoInst s rng ⦃ _ => True ⦄ ∧
      ∀ ss rng₁, States.send rngInst cryptoInst s rng = ok (.Ok ss, rng₁) →
        ((st.chain = none ∧ ∃ vn ∈ st.version_negotiation, vn.min_version.val ≤ 0) →
          ss.key = none ∧ serialize.States.into_pb ss.state ⦃ _ => True ⦄) ∧
        ∀ c : chain.Chain, (∃ cpb ∈ st.chain, fromPb cpb = .Ok c) ∨
            (st.chain = none ∧ ∃ vn ∈ st.version_negotiation, 0 < vn.min_version.val ∧
              chainFromVersionNegotiation vn = ok (.Ok c)) →
          0 < ss.msg.epoch.val ∧
          (∀ k ∈ ss.key,
            k.epoch.val = c.current_epoch.val + 1 ∧ c.links.buf.val.length < Usize.max) ∧
          ∀ c₁, (match ss.key with | none => c₁ = c | some k => c.add_epoch k = ok c₁) →
            ∀ ep : U64, ep.val + 1 = ss.msg.epoch.val →
            (c₁.send_epoch.val ≤ ep.val → ep.val ≤ c₁.current_epoch.val →
              c₁.current_epoch.val - ep.val ≤ Usize.max) ∧
            (c₁.send_epoch.val ≤ ep.val → ep.val ≤ c₁.current_epoch.val →
              c₁.current_epoch.val - ep.val < c₁.links.length.val →
              ∀ ce ∈ c₁.links.buf.val[c₁.links.head.val + chain.sendKeyIdx c₁ ep]?,
                ce.send.next.val.length = 32 ∧ ce.send.ctr.val < U32.max) ∧
            ∀ i mk c₂, c₁.send_key ep = ok (.Ok (i, mk), c₂) →
              serialize.States.into_pb ss.state ⦃ _ => True ⦄

/-! ## Spec theorem -/

/-- **Spec theorem for `spqr::send`**:

Under `SendAssumptions`, `send` never panics and returns a pair
`result : core.result.Result Send Error × R`. Its first component `result.1` is either `Ok` with
a `Send` value, holding the new state bytes (`state`), the serialised ratchet message (`msg`)
and the message key, if any (`key`), or `Err e` with an `Error`. Its second component
`result.2` is the random number generator handed back. Both are fixed by the stages `send`
passes through on the input bytes `state`:

- `decode_state` fails with `e`: `(Err e, rng)`. Otherwise it yields the protobuf state `st`,
  which all later stages read.
- `st` has no `inner` (the ratchet is disabled): `send` stops with
  `(Ok { state := Vec.new, msg := Vec.new, key := none }, rng)`: the state bytes and the ratchet
  message are empty, there is no message key, and `rng` is handed back untouched.
- `States::from_pb` on the `V1` inner state of `st` fails with `e`: `(Err e, rng)`.
- `States::send` fails with `e` and hands back the potentially updated `rng₁`: `(Err e, rng₁)`.
- `States::send` succeeds with `ss` (new inner state `ss.state`, ratchet message `ss.msg`,
  optional epoch secret `ss.key`) and `rng₁`: `result.2` is `rng₁`, and `result.1` depends on
  which chain `st` provides. Below, `vs` is `States::into_pb ss.state`, the new inner state as
  a protobuf struct.
  - `st.chain = none`, `st.version_negotiation = none`: `result.1 = Err ChainNotAvailable`.
  - `st.chain = none`, `st.version_negotiation = some vn`, `vn.min_version <= 0`: no chain is
    used, and `result.1 = Ok r` with
    `r.state = encode_state_pb { st with inner := some (.V1 vs) }`,
    `r.msg` the serialisation of `ss.msg` at ratchet index `0`, and
    `r.key = none`.
  - otherwise a chain is selected, with outcome `sel`: the model `fromPb cpb` of `Chain::from_pb`
    if `st.chain = some cpb`, else `chainFromVersionNegotiation vn` (`st.chain = none`,
    `vn.min_version > 0`). Then:
    - `sel = Err e`: `result.1 = Err e`.
    - `sel = Ok c`: `add_epoch` mixes the epoch secret `ss.key`, if any, into `c`, giving `c₁`,
      and `send_key` runs on `c₁` at epoch `ss.msg.epoch - 1`, returning its result `sk` and
      the chain `c₂` it leaves behind (`sendKeyPost` relates `c₁`, `sk` and `c₂`). If
      `sk = Err e`, `send_key` has left the chain unchanged, `c₂ = c₁`, and `result.1 = Err e`.
      If `sk = Ok (i, mk)` then `result.1 = Ok r` with
      `r.state = encode_state_pb { st with chain := some (intoPb c₂), inner := some (.V1 vs) }`,
      `r.msg` the serialisation of `ss.msg` at ratchet index `i`, and
      `r.key = some mk`.

**Source**: spqr/src/lib.rs (lines 271:0-331:1) -/
@[step]
theorem send_spec {R : Type} (rngInst : rand_1.rng.Rng R)
    (cryptoInst : rand_core_1.CryptoRng R) (state : alloc.vec.Vec U8) (rng : R)
    (h_assumptions : SendAssumptions rngInst cryptoInst state rng) :
    send rngInst cryptoInst state rng ⦃
      (result : (core.result.Result Send Error) × R) =>
      ∀ d, decode_state state = ok d → match d with
      | .Err e => result = (.Err e, rng)
      | .Ok st => match st.inner with
        | none => result = (.Ok { state := .new U8, msg := .new U8, key := none }, rng)
        | some (.V1 pb) => ∀ p, serialize.States.from_pb pb = ok p → match p with
          | .Err e => result = (.Err e, rng)
          | .Ok s => ∀ o rng₁, States.send rngInst cryptoInst s rng = ok (o, rng₁) → match o with
            | .Err e => result = (.Err e, rng₁)
            | .Ok ss =>
              result.2 = rng₁ ∧
              ((st.chain = none ∧ st.version_negotiation = none) →
                result.1 = .Err .ChainNotAvailable) ∧
              ((st.chain = none ∧ ∃ vn ∈ st.version_negotiation, vn.min_version.val ≤ 0) →
                ∃ r vs, result.1 = .Ok r ∧ serialize.States.into_pb ss.state = ok vs ∧
                  encode_state_pb { st with inner := some (.V1 vs) } = ok r.state ∧
                  decodesTo r.state { st with inner := some (.V1 vs) } ∧
                  r.msg.val.map UScalar.val = serialize.messageBytes ss.msg 0 ∧
                  r.key = none) ∧
              ∀ sel,
                (∃ cpb ∈ st.chain, fromPb cpb = sel) ∨
                  (st.chain = none ∧ ∃ vn ∈ st.version_negotiation, 0 < vn.min_version.val ∧
                    chainFromVersionNegotiation vn = ok sel) →
                match sel with
                | .Err e => result.1 = .Err e
                | .Ok c =>
                  ∃ c₁ ep sk c₂,
                    (match ss.key with | none => c₁ = c | some k => c.add_epoch k = ok c₁) ∧
                    ep.val + 1 = ss.msg.epoch.val ∧ c₁.send_key ep = ok (sk, c₂) ∧
                    chain.sendKeyPost c₁ ep sk c₂ ∧
                    match sk with
                    | .Err e => result.1 = .Err e
                    | .Ok (i, mk) =>
                      ∃ r vs, result.1 = .Ok r ∧ serialize.States.into_pb ss.state = ok vs ∧
                        encode_state_pb
                          { st with chain := some (intoPb c₂), inner := some (.V1 vs) } =
                            ok r.state ∧
                        decodesTo r.state
                          { st with chain := some (intoPb c₂), inner := some (.V1 vs) } ∧
                        r.msg.val.map UScalar.val = serialize.messageBytes ss.msg i.val ∧
                        r.key = some mk ⦄ := by
  have h_v0 : (0#i32 + 0#i32 : Result I32) = ok 0#i32 ∧ IScalar.cast .I32 0#i32 = 0#i32 := by
    obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists
      (IScalar.add_spec (x := 0#i32) (y := 0#i32) (by scalar_tac) (by scalar_tac))
    exact ⟨by rw [hz, show z = 0#i32 by scalar_tac], rfl⟩
  unfold send
  simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from, core.option.Option.as_ref, h_v0, bind_ok, lift, massert,
    alloc.vec.Vec.is_empty, alloc.vec.Vec.index_slice_index, core.convert.IntoFrom.into,
    U8.Insts.CoreConvertFromVersion.from]
  obtain ⟨d, hd, -⟩ := WP.spec_imp_exists (decode_state_spec state)
  rcases d with ⟨vno, cho, _ | ⟨⟨pb⟩⟩⟩ | e
  · simp only [hd, bind_ok]; simp [-IsEmpty.forall_iff, -IsEmpty.exists_iff]
  on_goal 2 => simp only [hd, bind_ok]; simp [-IsEmpty.forall_iff, -IsEmpty.exists_iff]
  obtain ⟨h_fp, h_assumptions⟩ := h_assumptions _ hd pb rfl
  obtain ⟨s | e, hr1, -⟩ := WP.spec_imp_exists h_fp
  on_goal 2 => simp only [hd, hr1, bind_ok]; simp [hr1, -IsEmpty.forall_iff, -IsEmpty.exists_iff]
  obtain ⟨h_st, h_assumptions⟩ := h_assumptions s hr1
  obtain ⟨⟨ss | e, rng₁⟩, hr2, -⟩ := WP.spec_imp_exists h_st
  on_goal 2 => simp only [hd, hr1, hr2, bind_ok, uncurry_apply_pair]; simp [hr1, hr2,
    -IsEmpty.forall_iff, -IsEmpty.exists_iff]
  obtain ⟨h_nc, h_cs⟩ := h_assumptions ss rng₁ hr2
  simp only [hd, hr1, hr2, bind_ok, uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq, and_imp,
    forall_apply_eq_imp_iff, forall_eq']
  have h_ser : ∀ idx, ∃ msg, serialize.Message.serialize ss.msg idx = ok msg ∧
      msg.val.map UScalar.val = serialize.messageBytes ss.msg idx.val ∧
      msg.val ≠ [] ∧ msg.index_usize 0#usize = ok 1#u8 := fun idx => by
    obtain ⟨msg, hmsg, hbytes⟩ := WP.spec_imp_exists (serialize.Message.serialize_spec ss.msg idx)
    obtain ⟨b, rest, hmv, hb, -⟩ := List.map_eq_cons_iff.mp hbytes
    exact ⟨msg, hmsg, hbytes, by simp [hmv],
      by simp [alloc.vec.Vec.index_usize, hmv, UScalar.eq_of_val_eq (j := 1#u8) hb]⟩
  by_cases hsrc : ∃ c : chain.Chain, (∃ cpb, cho = some cpb ∧ fromPb cpb = .Ok c) ∨
      (cho = none ∧ ∃ vn, vno = some vn ∧ 0 < vn.min_version.val ∧
        chainFromVersionNegotiation vn = ok (.Ok c))
  · obtain ⟨c, hcs⟩ := hsrc
    obtain ⟨h_e1, h_add, h_sk⟩ := h_cs c hcs
    have hwf : c.links.head.val + c.links.length.val ≤ c.links.buf.val.length := by
      rcases hcs with ⟨cpb, -, hc⟩ | ⟨-, vn, -, -, hc⟩
      · clear * - hc; grind [fromPb]
      unfold chainFromVersionNegotiation at hc
      (split at hc <;> try split at hc) <;> try simp at hc
      clear * - hc; grind [(WP.spec_ok _).mp (hc ▸ chain.Chain.new_spec _ _ _)]
    obtain ⟨c₁, hmix, hwf₁⟩ : ∃ c₁,
        (match ss.key with | none => c₁ = c | some k => c.add_epoch k = ok c₁) ∧
        c₁.links.head.val + c₁.links.length.val ≤ c₁.links.buf.val.length := by
      rcases hk : ss.key with _ | k
      · exact ⟨c, rfl, hwf⟩
      obtain ⟨c₁, hc₁, h⟩ := WP.spec_imp_exists
        ((h_add k hk).elim (chain.Chain.add_epoch_spec c k · (by omega) ·))
      exact ⟨c₁, hc₁, by clear * - h hwf; grind⟩
    obtain ⟨e, he, he'⟩ := WP.spec_imp_exists (U64.sub_spec (y := 1#u64) h_e1)
    have he1 : e.val + 1 = ss.msg.epoch.val := by rw [he'.1]; exact Nat.sub_add_cancel h_e1
    obtain ⟨h_df, h_tg, h_ip⟩ := h_sk c₁ hmix e he1
    obtain ⟨⟨r₄, c₂⟩, hsk, hpost⟩ := WP.spec_imp_exists
      (chain.Chain.send_key_spec c₁ e h_df hwf₁ fun h₁ h₂ h₃ => by
        split <;> [trivial; exact h_tg h₁ h₂ h₃ _ ‹_›])
    have h_ok : ∀ i mk, r₄ = .Ok (i, mk) →
        c₂.links.head.val + c₂.links.length.val ≤ c₂.links.buf.val.length ∧ mk.val ≠ [] := by
      clear * - hpost; grind [chain.sendKeyPost, chain.sendKeyDequePost, chain.sendKeySlotPost]
    rcases hcs with ⟨cpb, rfl, hsel⟩ | ⟨rfl, vn, rfl, hsel⟩
    on_goal 1 =>
      obtain ⟨r3, hr3, rfl⟩ := WP.spec_imp_exists (chain.Chain.from_pb_spec cpb)
      simp only [hr3, hsel, bind_ok]
    on_goal 2 =>
      obtain ⟨r3, hr3, hcf⟩ := WP.spec_imp_exists (chain_from_version_negotiation_spec vn)
      cases Result.ok_injective (hcf.symm.trans hsel.2)
      simp only [show vn.min_version > 0#i32 from hsel.1, decide_true, Bool.true_or,
        ↓reduceIte, hr3, bind_ok]
    all_goals
      simp only [hsel, reduceCtorEq, false_implies, implies_true, Option.some.injEq,
        Option.mem_def, forall_eq', false_and, true_and, exists_eq_left', or_false, false_or,
        Result.ok.injEq, ← Int.not_lt, not_true_eq_false, exists_false]
      refine WP.spec_bind (Pₘ := (c₁ = ·)) ?_ fun _ h => h ▸ ?_
      · rcases hk : ss.key with _ | k <;> simp only [hk] at hmix <;> simp [hmix]
      simp only [he, hsk, bind_ok, uncurry_apply_pair]
      rcases r₄ with ⟨⟨i, mk⟩⟩ | err
      · obtain ⟨hwf₂, hmk⟩ := h_ok i mk rfl
        obtain ⟨vs, hvs, -⟩ := WP.spec_imp_exists (h_ip i mk c₂ hsk)
        obtain ⟨msg, hmsg, hbytes, hne, hidx⟩ := h_ser i
        obtain ⟨cp, hcp, rfl⟩ := WP.spec_imp_exists (chain.Chain.into_pb_spec c₂ hwf₂)
        simp only [hcp, hmsg, List.isEmpty_iff, hne, hidx, hvs, hmk, bind_ok, uncurry_apply_pair,
          not_false_eq_true, ↓reduceIte]
        refine WP.spec_bind (WP.spec_refl (encode_state_pb_spec _)) fun v ⟨hdec, hv⟩ =>
          (WP.spec_ok _).mpr ?_
        exact ⟨rfl, _, _, _, _, hmix, he1, hsk, hpost, _, vs, rfl, rfl, hv, hdec, hbytes, rfl⟩
      · simp only [bind_ok, bind_tc_ok, WP.spec_ok, true_and]
        exact ⟨_, _, _, _, hmix, he1, hsk, hpost, rfl⟩
  · rcases cho with _ | cpb
    · rcases vno with _ | vn
      · exact (WP.spec_ok _).mpr ⟨rfl, fun _ _ => rfl, (fun _ ⟨_, h, _⟩ => nomatch h),
          fun | _, .inl ⟨_, h, _⟩ | _, .inr ⟨_, _, h, _⟩ => nomatch h⟩
      by_cases h_mv : 0 < vn.min_version.val
      · obtain ⟨c | e, hr3, hcf⟩ := WP.spec_imp_exists (chain_from_version_negotiation_spec vn)
        · exact (hsrc ⟨c, .inr ⟨rfl, vn, rfl, h_mv, hcf⟩⟩).elim
        simp [hr3, hcf, h_mv, -IsEmpty.forall_iff, -IsEmpty.exists_iff]
      · obtain ⟨h_key, h_ip⟩ := h_nc ⟨rfl, vn, rfl, by omega⟩
        obtain ⟨vs, hvs, -⟩ := WP.spec_imp_exists h_ip
        obtain ⟨msg, hmsg, hbytes, hne, hidx⟩ := h_ser 0#u32
        obtain ⟨v, hv, hdec⟩ :=
          WP.spec_imp_exists (encode_state_pb_spec ⟨some vn, none, some (.V1 vs)⟩)
        simp [h_key, h_mv, core.option.Option.is_none, hmsg, hne, hidx,
          hvs, hv, hbytes, hdec, -IsEmpty.forall_iff, -IsEmpty.exists_iff]
    · obtain ⟨c | e, hr3, hfp⟩ := WP.spec_imp_exists (chain.Chain.from_pb_spec cpb)
      · exact (hsrc ⟨c, .inl ⟨cpb, rfl, hfp.symm⟩⟩).elim
      simp only [hr3, bind_ok, bind_tc_ok]
      simp [← hfp, -IsEmpty.forall_iff, -IsEmpty.exists_iff]

end spqr
