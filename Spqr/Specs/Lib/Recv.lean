/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Lib.StatePb
import Spqr.Specs.Lib.MsgPreamble
import Spqr.Specs.Lib.ChainFrom
import Spqr.Specs.Proto.PqRatchet.Direction.TryFrom
import Spqr.Specs.Aeneas.VecIndexRangeFull
import Spqr.Auxiliary.Aeneas.SpecImpExists
/-!
# Spec theorem for `spqr::recv`

`recv` is the top-level receive entry point of the SPQR post-quantum ratchet.  Given a
serialized protocol state (`state : Vec<u8>`) and an incoming message (`msg : Vec<u8>`), it:

  1. Parses the message preamble via `msg_preamble`.
  2. Decodes the persisted state via `decode_state`.
  3. Determines the current protocol version via `state_version`.
  4. Performs version negotiation / compatibility checks:
     - Message version below minimum → `Err MinimumVersion`.
     - Version mismatch without negotiation → `Err VersionMismatch`.
     - Current version V0 (disabled) → `Ok { state = [], key = none }`.
  5. Same-version path: deserializes chunked-states, calls `States.recv`, reconstructs the
     ratchet chain via `chain_from`, optionally `Chain.add_epoch`, derives the message key
     via `Chain.recv_key`, re-serializes via `encode_state_pb`.

## Organisation

Each control-flow path of the Rust function gets

* an **equational lemma** `recv_eq_<path>` (`recv state msg = <explicit computation>`), proved
  by unfolding the translation, and
* a **spec theorem** `recv_spec_<path>` in the usual `⦃ ⦄` form, derived from it.

The path theorems are not tagged `@[step]`: their hypotheses are equations on the results of
`msg_preamble`/`decode_state` rather than WP specs, so `step` cannot select them.  The two
`@[step]` contracts are `recv_spec_v0` (empty inputs) and the total `recv_spec`, which only
assumes that `recv` does not panic and derives the shape of every possible result.

| Path (Rust)                                       | Spec theorem(s)                              |
|---------------------------------------------------|----------------------------------------------|
| `msg_preamble(msg)?` fails                        | `recv_spec_msg_preamble_err`                 |
| `decode_state(state)?` fails                      | `recv_spec_decode_state_err`                 |
| `msg.version < min_version`, `vn = None`          | `recv_spec_minimum_version_no_negotiation`   |
| `msg.version < min_version`, `vn = Some`          | `recv_spec_minimum_version_negotiating`      |
| `msg.version != current && !still_negotiating`    | `recv_spec_version_mismatch`                 |
| `current_version == 0`                            | `recv_spec_v0`, `recv_spec_empty_state`,     |
|                                                   | `recv_spec_v0_no_negotiation`,               |
|                                                   | `recv_spec_v0_negotiating`                   |
| `Ordering::Greater` (epoch-0 key, keep `vn`)      | `recv_spec_greater`                          |
| `Ordering::Less` (downgrade to V0)                | `recv_spec_less_v0`                          |
| `Ordering::Equal`, `Inner::V1`                    | `recv_spec_equal_v1_no_negotiation`,         |
|   (postcondition `recvV1Post`)                    | `recv_spec_equal_v1_negotiating`             |

**Source**: spqr/src/lib.rs (lines 361:0-490:1)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr

/-- The canonical V0 (disabled) receive result: empty state, no key. -/
def recvV0Result : core.result.Result Recv Error :=
  .Ok { state := alloc.vec.Vec.new U8, key := none }

/-- Postcondition for a **non-empty** successful `recv` result: the new serialized state is the
protobuf encoding of a state that carries a chain (`chain = Some`) and a V1 inner state
(`inner = Some (V1 _)`).  Moreover either

* `version_negotiation = None` and an absent key means the derived message key was empty
  (same-version path, `Ordering::Equal`), or
* `version_negotiation = Some vn` is **kept** and the key is always present
  (`Ordering::Greater`, their version is newer than ours). -/
def recvOkPost (r : Recv) : Prop :=
  ∃ st : proto.pq_ratchet.PqRatchetState,
    encode_state_pb st = ok r.state ∧
    (∃ c, st.chain = some c) ∧
    (∃ pb, st.inner = some (.V1 pb)) ∧
    ((st.version_negotiation = none ∧ ∀ k, r.key = some k → k.val ≠ []) ∨
     (∃ vn, st.version_negotiation = some vn ∧ ∃ k, r.key = some k))

/-- **Total postcondition for `spqr.recv`**: every successful result is either the empty
V0 result or satisfies `recvOkPost`.  Application errors are passed through unchanged from the
sub-calls, so nothing beyond `Err` is claimed about them here. -/
def recvPost (result : core.result.Result Recv Error) : Prop :=
  match result with
  | .Ok r => r = { state := alloc.vec.Vec.new U8, key := none } ∨ recvOkPost r
  | .Err _ => True

/-- **Spec theorem for `spqr.recv`** (V0 / disabled path):

When both state and message are empty, `recv` returns the empty-state result with no key.

**Source**: spqr/src/lib.rs (lines 361:0-490:1) -/
@[step]
theorem recv_spec_v0 (state msg : alloc.vec.Vec U8)
    (h_empty : state.val = [])
    (h_msg_empty : msg.val = []) :
    recv state msg ⦃ (result : core.result.Result Recv Error) =>
      result = recvV0Result ⦄ := by
  -- An empty message parses to the default preamble (`version = 0`).
  have hpre : ∃ mp : MsgPreamble, msg_preamble msg = ok (.Ok mp) ∧ mp.version = 0#u8 := by
    unfold msg_preamble
    simp only [alloc.vec.Vec.is_empty, bind_ok, List.isEmpty_iff, h_msg_empty, ↓reduceIte]
    obtain ⟨s, hs, -⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_RangeFull_spec msg)
    rw [hs]
    exact ⟨{ version := 0#u8, epoch := 0#u64, index := 0#u32, remaining := s }, by simp, rfl⟩
  obtain ⟨mp, hpre, hmpv⟩ := hpre
  -- An empty state decodes to the default state (all `none`).
  have hdec : decode_state state =
      ok (.Ok { version_negotiation := none, chain := none, inner := none }) := by
    unfold decode_state
    simp [alloc.vec.Vec.is_empty, h_empty]
  -- The discriminant of `V0` cast to `u8` is `0`.
  have hcv : IScalar.hcast UScalarTy.U8 (read_discriminant proto.pq_ratchet.Version.V0) = 0#u8 := by
    decide
  unfold recv
  rw [hpre, hdec]
  simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, state_version, hcv, hmpv, lift,
    ↓reduceIte]
  step*
  -- Only the trivial `match 0#u8 with | 0 => ok true | _ => ok false` remains before the result.
  split <;> simp [recvV0Result]

/-! ## Helper lemmas on the version discriminants -/

/-- `Version::V0 as u8 = 0` (the discriminant cast used by `recv`). -/
theorem Version.V0_discriminant_u8 :
    IScalar.hcast UScalarTy.U8 (read_discriminant proto.pq_ratchet.Version.V0) = 0#u8 := by
  decide

/-- `Version::V1 as u8 = 1` (the discriminant cast used by `recv`). -/
theorem Version.V1_discriminant_u8 :
    IScalar.hcast UScalarTy.U8 (read_discriminant proto.pq_ratchet.Version.V1) = 1#u8 := by
  decide

/-! ## Error propagation (`?` on `msg_preamble` / `decode_state`) -/

/-- **Equational lemma for `spqr.recv`** (message decode failure):
`let msg = msg_preamble(msg)?;` — an `Err` from `msg_preamble` is returned unchanged. -/
theorem recv_eq_msg_preamble_err (state msg : alloc.vec.Vec U8) (e : Error)
    (hpre : msg_preamble msg = ok (.Err e)) :
    recv state msg = ok (.Err e) := by
  unfold recv
  rw [hpre]
  simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from]

/-- **Equational lemma for `spqr.recv`** (state decode failure):
`let prenegotiated_state_pb = decode_state(state)?;` — an `Err` from `decode_state` is returned
unchanged. -/
theorem recv_eq_decode_state_err (state msg : alloc.vec.Vec U8) (mp : MsgPreamble) (e : Error)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state = ok (.Err e)) :
    recv state msg = ok (.Err e) := by
  unfold recv
  rw [hpre]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [hdec]
  simp [
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from]

/-! ## Version negotiation checks -/

/-- **Equational lemma for `spqr.recv`** (`MinimumVersion`, no negotiation):
Without a `version_negotiation` the minimum version is the current version
(`innerVersion st`); a message below it is rejected with `Err MinimumVersion`. -/
theorem recv_eq_minimum_version_no_negotiation (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (ch : Option proto.pq_ratchet.Chain)
    (pb : proto.pq_ratchet.V1State)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := none, chain := ch, inner := some (.V1 pb) }))
    (hlt : mp.version.val < 1) :
    recv state msg = ok (.Err Error.MinimumVersion) := by
  have hv : mp.version.val = 0 := by omega
  unfold recv
  rw [hpre]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [hdec]
  simp only [bind_ok, state_version, Version.V1_discriminant_u8, lift]
  split <;> simp [hv]

/-- **Equational lemma for `spqr.recv`** (`MinimumVersion`, still negotiating):
With a `version_negotiation` the minimum version is `vn.min_version as u8`; a message below it
is rejected with `Err MinimumVersion`, regardless of the current version. -/
theorem recv_eq_minimum_version_negotiating (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (vn : proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (ch : Option proto.pq_ratchet.Chain) (inner : Option proto.pq_ratchet.pq_ratchet_state.Inner)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := some vn, chain := ch, inner := inner }))
    (hlt : mp.version < IScalar.hcast .U8 vn.min_version) :
    recv state msg = ok (.Err Error.MinimumVersion) := by
  unfold recv
  rw [hpre]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [hdec]
  simp only [bind_ok, state_version, lift]
  cases inner <;> simp only [bind_ok] <;> change (if mp.version < _ then _ else _) = _ <;>
    rw [ite_eq_left hlt]

/-- **Equational lemma for `spqr.recv`** (`VersionMismatch`):
Without a `version_negotiation` and with a V1 state (so negotiation is over), any message whose
version differs from `1` (and is not below it) is rejected with `Err VersionMismatch`. -/
theorem recv_eq_version_mismatch (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (ch : Option proto.pq_ratchet.Chain)
    (pb : proto.pq_ratchet.V1State)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := none, chain := ch, inner := some (.V1 pb) }))
    (hgt : 1 < mp.version.val) :
    recv state msg = ok (.Err Error.VersionMismatch) := by
  have h0 : mp.version.val ≠ 0 := by omega
  have h1 : mp.version.val ≠ 1 := by omega
  unfold recv
  rw [hpre]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [hdec]
  simp only [bind_ok, state_version, Version.V1_discriminant_u8, lift]
  split
  · rename_i heq; exact absurd heq (by decide)
  · simp [h0, h1]

/-! ## The V0 (disabled) path -/

/-- **Equational lemma for `spqr.recv`** (V0, no negotiation):
A state with `inner = None` and no `version_negotiation` has current version `0`, so
`min_version = 0` and negotiation is still open; **any** successfully parsed message yields the
empty result `Ok { state = [], key = None }`. -/
theorem recv_eq_v0_no_negotiation (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (ch : Option proto.pq_ratchet.Chain)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := none, chain := ch, inner := none })) :
    recv state msg = ok recvV0Result := by
  unfold recv
  rw [hpre]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [hdec]
  simp only [bind_ok, state_version, Version.V0_discriminant_u8, lift]
  split
  · simp [recvV0Result]
  · rename_i h; exact absurd rfl h

/-- **Equational lemma for `spqr.recv`** (V0, still negotiating):
A state with `inner = None` but a `version_negotiation` has current version `0`; a message at
or above `vn.min_version` yields the empty result `Ok { state = [], key = None }`. -/
theorem recv_eq_v0_negotiating (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (vn : proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (ch : Option proto.pq_ratchet.Chain)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := some vn, chain := ch, inner := none }))
    (hge : ¬ mp.version < IScalar.hcast .U8 vn.min_version) :
    recv state msg = ok recvV0Result := by
  unfold recv
  rw [hpre]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [hdec]
  simp only [bind_ok, state_version, Version.V0_discriminant_u8, lift]
  change (if mp.version < _ then _ else _) = _
  rw [ite_eq_right hge]
  simp [recvV0Result]

/-- **Spec theorem for `spqr.recv`** (empty persisted state, arbitrary message):
An empty state decodes to the all-`none` state, so the result is the empty V0 result whenever
the message preamble parses, and `Err MsgDecode` otherwise. -/
theorem recv_spec_empty_state (state msg : alloc.vec.Vec U8)
    (h_empty : state.val = []) :
    recv state msg ⦃ (result : core.result.Result Recv Error) =>
      result = recvV0Result ∨ result = .Err Error.MsgDecode ⦄ := by
  have hdec : decode_state state =
      ok (.Ok { version_negotiation := none, chain := none, inner := none }) := by
    unfold decode_state
    simp [alloc.vec.Vec.is_empty, h_empty]
  obtain ⟨r, hr, hpost⟩ := WP.spec_imp_exists (msg_preamble_spec msg)
  cases r with
  | Ok mp =>
    rw [recv_eq_v0_no_negotiation state msg mp none hr hdec]
    simp
  | Err e =>
    rw [recv_eq_msg_preamble_err state msg e hr]
    simp only at hpost
    simp [hpost]

/-! ## `Ordering::Greater`: their version is higher, we stay negotiable -/

/-- **Equational lemma for `spqr.recv`** (`Ordering::Greater`):
State is V1 with a pending `version_negotiation`, and the message version is `> 1` (and not
below `vn.min_version`).  Then `recv`
* rebuilds the chain via `chain_from st.chain (Some vn)` (an `Err` is propagated),
* pulls the key from **epoch 0** with `chain.recv_key(0, msg.index)` (an `Err` is propagated),
* returns `Ok { key = Some k, state = encode { chain = Some chain'.into_pb(),
  version_negotiation = Some vn (kept), inner = Some (V1 pb) (kept) } }`. -/
theorem recv_eq_greater (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (vn : proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (ch : Option proto.pq_ratchet.Chain) (pb : proto.pq_ratchet.V1State)
    (cr : core.result.Result chain.Chain Error)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := some vn, chain := ch, inner := some (.V1 pb) }))
    (hge : ¬ mp.version < IScalar.hcast .U8 vn.min_version)
    (hgt : 1 < mp.version.val)
    (hchain : chain_from ch (some vn) = ok cr) :
    recv state msg =
      (match cr with
      | .Err e => ok (.Err e)
      | .Ok c => do
        let (kr, c') ← chain.Chain.recv_key c 0#u64 mp.index
        match kr with
        | .Err e => ok (.Err e)
        | .Ok k =>
          let cpb ← chain.Chain.into_pb c'
          let bytes ← encode_state_pb
            { version_negotiation := some vn, chain := some cpb, inner := some (.V1 pb) }
          ok (.Ok { state := bytes, key := some k })) := by
  have h1 : mp.version.val ≠ 1 := by omega
  have hcmp : compare mp.version.val 1 = Ordering.gt := Nat.compare_eq_gt.mpr hgt
  unfold recv
  rw [hpre]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [hdec]
  simp only [bind_ok, state_version, Version.V1_discriminant_u8, lift]
  change (if mp.version < _ then _ else _) = _
  rw [ite_eq_right hge]
  simp only [bne_iff_ne, ne_eq, core.cmp.impls.OrdU8.cmp, core.option.Option.as_ref, bind_ok,
    recv.ZERO_EPOCH, hchain, massert]
  simp only [UScalar.neq_to_neq_val, UScalar.ofNatCore_val_eq, ↓reduceIte, Nat.not_eq, ne_eq,
    one_ne_zero, not_false_eq_true, zero_ne_one, not_lt_zero, Order.lt_one_iff, or_true, or_self,
    UScalar.val_not_eq_imp_not_eq, h1, hcmp]
  cases cr with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
  | Ok c =>
    simp only [bind_ok]
    congr 1
    funext ⟨kr, c'⟩
    cases kr <;> simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]

/-! ## `Ordering::Less`: negotiate down to their version -/

/-- **Equational lemma for `spqr.recv`** (`Ordering::Less`, downgrade to V0):
State is V1 with a pending `version_negotiation` and the message is V0 (at or above
`vn.min_version`).  Both `assert!`s hold, the `expect`s succeed, the direction is parsed from
`vn.direction` (`Err StateDecode` on an unknown value), `init_inner V0 _ _ = None`, the chain is
rebuilt via `chain_from st.chain (Some vn)` (errors propagated) and `into_pb`'d; since the new
`inner` is `None` the result is the empty `Ok { state = [], key = None }`. -/
theorem recv_eq_less_v0 (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (vn : proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (ch : Option proto.pq_ratchet.Chain) (pb : proto.pq_ratchet.V1State)
    (dr : core.result.Result proto.pq_ratchet.Direction prost.error.UnknownEnumValue)
    (cr : core.result.Result chain.Chain Error)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := some vn, chain := ch, inner := some (.V1 pb) }))
    (hge : ¬ mp.version < IScalar.hcast .U8 vn.min_version)
    (hv0 : mp.version.val = 0)
    (hdir : proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from
      vn.direction = ok dr)
    (hchain : chain_from ch (some vn) = ok cr) :
    recv state msg =
      (match dr with
      | .Err _e => ok (.Err Error.StateDecode)
      | .Ok _d =>
        match cr with
        | .Err e => ok (.Err e)
        | .Ok c => do
          let _cpb ← chain.Chain.into_pb c
          ok recvV0Result) := by
  have hcmp : compare (0 : Nat) 1 = Ordering.lt := by decide
  replace hv0 : mp.version = 0#u8 := by scalar_tac
  unfold recv
  rw [hpre]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [hdec]
  simp only [bind_ok, state_version, Version.V1_discriminant_u8, lift]
  change (if mp.version < _ then _ else _) = _
  rw [ite_eq_right hge]
  simp only [bne_iff_ne, ne_eq, core.cmp.impls.OrdU8.cmp, bind_ok, massert, hv0,
    core.option.Option.expect, Result.ofOption, core.result.Result.expect, init_inner, hdir]
  simp only [Nat.not_eq, UScalar.ofNatCore_val_eq, ne_eq, zero_ne_one, not_false_eq_true,
    one_ne_zero, Order.lt_one_iff, not_lt_zero, or_false, or_self, UScalar.val_not_eq_imp_not_eq,
    ↓reduceIte, or_true, gt_iff_lt, UScalar.lt_equiv, bind_ok, hcmp]
  have htf : proto.pq_ratchet.Version.Insts.CoreConvertTryFromU8String.try_from 0#u8 =
      ok (.Ok proto.pq_ratchet.Version.V0) := by
    unfold proto.pq_ratchet.Version.Insts.CoreConvertTryFromU8String.try_from
    rfl
  rw [htf]
  simp only [bind_ok]
  cases dr with
  | Err e =>
    simp [core.result.Result.map_err,
      recv.closure.Insts.CoreOpsFunctionFnOnceTupleUnknownEnumValueError.call_once,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
  | Ok d =>
    simp only [core.result.Result.map_err, bind_ok, hchain]
    cases cr with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from]
    | Ok c =>
      simp [recvV0Result]

/-! ## `Ordering::Equal`: same version, process the message -/

/-- Monadic functional model of the same-version V1 receive tail:
`Message::deserialize(epoch, remaining)` → `States::from_pb` → `States::recv` →
`chain_from` → optional `add_epoch` → `recv_key (epoch - 1) index` → re-encode with
`version_negotiation = None`; the key is dropped when empty.  Every `?` propagates its error. -/
noncomputable def recvV1Model (mp : MsgPreamble)
    (vn : Option proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (ch : Option proto.pq_ratchet.Chain) (pb : proto.pq_ratchet.V1State) :
    Result (core.result.Result Recv Error) := do
  let mr ← v1.chunked.states.serialize.Message.deserialize mp.epoch mp.remaining
  match mr with
  | .Err e => ok (.Err e)
  | .Ok scka_msg =>
    let sr ← v1.chunked.states.serialize.States.from_pb pb
    match sr with
    | .Err e => ok (.Err e)
    | .Ok states =>
      let rr ← v1.chunked.states.States.recv states scka_msg
      match rr with
      | .Err e => ok (.Err e)
      | .Ok r =>
        let msg_key_epoch ← mp.epoch - 1#u64
        let cr ← chain_from ch vn
        match cr with
        | .Err e => ok (.Err e)
        | .Ok c =>
          let c1 ← match r.key with
            | none => ok c
            | some epoch_secret => chain.Chain.add_epoch c epoch_secret
          let (kr, c2) ← chain.Chain.recv_key c1 msg_key_epoch mp.index
          match kr with
          | .Err e => ok (.Err e)
          | .Ok k =>
            let vs ← v1.chunked.states.serialize.States.into_pb r.state
            let cpb ← chain.Chain.into_pb c2
            let bytes ← encode_state_pb
              { version_negotiation := none, chain := some cpb, inner := some (.V1 vs) }
            let b ← alloc.vec.Vec.is_empty Global k
            if b then ok (.Ok { state := bytes, key := none })
            else ok (.Ok { state := bytes, key := some k })

/-- **Equational lemma for `spqr.recv`** (`Ordering::Equal`, V1, no negotiation):
State is V1 without `version_negotiation` and the message is V1.  The result is exactly
`recvV1Model mp none ch pb`: the chain is rebuilt from `st.chain` only (no `vn` fallback), and
the re-encoded state has `version_negotiation = None`. -/
theorem recv_eq_equal_v1_no_negotiation (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (ch : Option proto.pq_ratchet.Chain)
    (pb : proto.pq_ratchet.V1State)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := none, chain := ch, inner := some (.V1 pb) }))
    (hv1 : mp.version.val = 1) :
    recv state msg = recvV1Model mp none ch pb := by
  replace hv1 : mp.version = 1#u8 := by scalar_tac
  have hcmp11 : compare (1#u8).val (1#u8).val = Ordering.eq := by simp
  unfold recv recvV1Model
  rw [hpre]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [hdec]
  simp only [bind_ok, state_version, Version.V1_discriminant_u8, lift]
  split
  · rename_i heq; exact absurd heq (by decide)
  simp only [bind_ok]
  change (if mp.version < _ then _ else _) = _
  rw [ite_eq_right (hv1 ▸ lt_irrefl _)]
  simp only [hv1, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [ite_eq_right (by decide)]
  simp only [core.cmp.impls.OrdU8.cmp, core.option.Option.as_ref, hcmp11, bind_ok,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from]
  congr 1; funext mr; cases mr with
  | Err e => simp
  | Ok scka_msg =>
  simp only [bind_ok]
  congr 1; funext sr; cases sr with
  | Err e => simp
  | Ok states =>
  simp only [bind_ok]
  congr 1; funext rr; cases rr with
  | Err e => simp
  | Ok r =>
  simp only [bind_ok]
  congr 1; funext msg_key_epoch
  congr 1; funext cr; cases cr with
  | Err e => simp
  | Ok c =>
  simp only [bind_ok]
  congr 1; funext c1
  congr 1; funext ⟨kr, c2⟩; cases kr with
  | Err e => simp
  | Ok k => simp

/-- **Equational lemma for `spqr.recv`** (`Ordering::Equal`, V1, still negotiating):
State is V1 with a pending `version_negotiation` and the message is V1 (at or above
`vn.min_version`).  The result is exactly `recvV1Model mp (some vn) ch pb`: the chain may be
rebuilt from `vn` when `st.chain = None`, and the re-encoded state **clears** the negotiation. -/
theorem recv_eq_equal_v1_negotiating (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (vn : proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (ch : Option proto.pq_ratchet.Chain) (pb : proto.pq_ratchet.V1State)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := some vn, chain := ch, inner := some (.V1 pb) }))
    (hge : ¬ mp.version < IScalar.hcast .U8 vn.min_version)
    (hv1 : mp.version.val = 1) :
    recv state msg = recvV1Model mp (some vn) ch pb := by
  replace hv1 : mp.version = 1#u8 := by scalar_tac
  have hcmp11 : compare (1#u8).val (1#u8).val = Ordering.eq := by simp
  unfold recv recvV1Model
  rw [hpre]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [hdec]
  simp only [bind_ok, state_version, Version.V1_discriminant_u8, lift]
  change (if mp.version < _ then _ else _) = _
  rw [if_neg hge]
  simp only [hv1, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_ok,
    core.cmp.impls.OrdU8.cmp, core.option.Option.as_ref]
  rw [if_neg (by decide)]
  simp only [hcmp11,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from]
  congr 1; funext mr; cases mr with
  | Err e => simp
  | Ok scka_msg =>
  simp only [bind_ok]
  congr 1; funext sr; cases sr with
  | Err e => simp
  | Ok states =>
  simp only [bind_ok]
  congr 1; funext rr; cases rr with
  | Err e => simp
  | Ok r =>
  simp only [bind_ok]
  congr 1; funext msg_key_epoch
  congr 1; funext cr; cases cr with
  | Err e => simp
  | Ok c =>
  simp only [bind_ok]
  congr 1; funext c1
  congr 1; funext ⟨kr, c2⟩; cases kr with
  | Err e => simp
  | Ok k => simp

/-! ## Spec theorems (`⦃ ⦄` form) derived from the equational lemmas above -/

/-- **Spec theorem for `spqr.recv`** (message decode failure):
`let msg = msg_preamble(msg)?;` — an `Err` from `msg_preamble` is returned unchanged. -/
theorem recv_spec_msg_preamble_err (state msg : alloc.vec.Vec U8) (e : Error)
    (hpre : msg_preamble msg = ok (.Err e)) :
    recv state msg ⦃ (result : core.result.Result Recv Error) => result = .Err e ⦄ := by
  rw [recv_eq_msg_preamble_err state msg e hpre]; simp

/-- **Spec theorem for `spqr.recv`** (state decode failure):
`decode_state(state)?` — an `Err` from `decode_state` is returned unchanged. -/
theorem recv_spec_decode_state_err (state msg : alloc.vec.Vec U8) (mp : MsgPreamble) (e : Error)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state = ok (.Err e)) :
    recv state msg ⦃ (result : core.result.Result Recv Error) => result = .Err e ⦄ := by
  rw [recv_eq_decode_state_err state msg mp e hpre hdec]; simp

/-- **Spec theorem for `spqr.recv`** (`MinimumVersion`, no negotiation):
V1 state without `version_negotiation`, message version `< 1` → `Err MinimumVersion`. -/
theorem recv_spec_minimum_version_no_negotiation (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (ch : Option proto.pq_ratchet.Chain) (pb : proto.pq_ratchet.V1State)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := none, chain := ch, inner := some (.V1 pb) }))
    (hlt : mp.version.val < 1) :
    recv state msg ⦃ (result : core.result.Result Recv Error) =>
      result = .Err Error.MinimumVersion ⦄ := by
  rw [recv_eq_minimum_version_no_negotiation state msg mp ch pb hpre hdec hlt]; simp

/-- **Spec theorem for `spqr.recv`** (`MinimumVersion`, still negotiating):
message version `< vn.min_version as u8` → `Err MinimumVersion`, whatever `inner` is. -/
theorem recv_spec_minimum_version_negotiating (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (vn : proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (ch : Option proto.pq_ratchet.Chain) (inner : Option proto.pq_ratchet.pq_ratchet_state.Inner)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := some vn, chain := ch, inner := inner }))
    (hlt : mp.version < IScalar.hcast .U8 vn.min_version) :
    recv state msg ⦃ (result : core.result.Result Recv Error) =>
      result = .Err Error.MinimumVersion ⦄ := by
  rw [recv_eq_minimum_version_negotiating state msg mp vn ch inner hpre hdec hlt]; simp

/-- **Spec theorem for `spqr.recv`** (`VersionMismatch`):
V1 state without `version_negotiation`, message version `> 1` → `Err VersionMismatch`. -/
theorem recv_spec_version_mismatch (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (ch : Option proto.pq_ratchet.Chain) (pb : proto.pq_ratchet.V1State)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := none, chain := ch, inner := some (.V1 pb) }))
    (hgt : 1 < mp.version.val) :
    recv state msg ⦃ (result : core.result.Result Recv Error) =>
      result = .Err Error.VersionMismatch ⦄ := by
  rw [recv_eq_version_mismatch state msg mp ch pb hpre hdec hgt]; simp

/-- **Spec theorem for `spqr.recv`** (V0, no negotiation): any parsed message → empty result. -/
theorem recv_spec_v0_no_negotiation (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (ch : Option proto.pq_ratchet.Chain)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := none, chain := ch, inner := none })) :
    recv state msg ⦃ (result : core.result.Result Recv Error) => result = recvV0Result ⦄ := by
  rw [recv_eq_v0_no_negotiation state msg mp ch hpre hdec]; simp

/-- **Spec theorem for `spqr.recv`** (V0, still negotiating):
message at or above `vn.min_version` → empty result. -/
theorem recv_spec_v0_negotiating (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (vn : proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (ch : Option proto.pq_ratchet.Chain)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := some vn, chain := ch, inner := none }))
    (hge : ¬ mp.version < IScalar.hcast .U8 vn.min_version) :
    recv state msg ⦃ (result : core.result.Result Recv Error) => result = recvV0Result ⦄ := by
  rw [recv_eq_v0_negotiating state msg mp vn ch hpre hdec hge]; simp

/-- **Spec theorem for `spqr.recv`** (`Ordering::Greater`):
V1 state with pending negotiation and message version `> 1`.  On success the result carries
the key pulled from **epoch 0** (`chain.recv_key(0, msg.index)`), the chain comes from
`chain_from st.chain (Some vn)`, and the re-encoded state **keeps** `version_negotiation = Some vn`
and `inner = Some (V1 pb)`.  Errors of `chain_from` / `recv_key` are propagated verbatim.
Requires that `recv_key` and `into_pb` do not panic on the reconstructed chain. -/
theorem recv_spec_greater (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (vn : proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (ch : Option proto.pq_ratchet.Chain) (pb : proto.pq_ratchet.V1State)
    (cr : core.result.Result chain.Chain Error)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := some vn, chain := ch, inner := some (.V1 pb) }))
    (hge : ¬ mp.version < IScalar.hcast .U8 vn.min_version)
    (hgt : 1 < mp.version.val)
    (hchain : chain_from ch (some vn) = ok cr)
    (hkey : ∀ c, cr = .Ok c → chain.Chain.recv_key c 0#u64 mp.index ⦃ _ => True ⦄)
    (hpb : ∀ c, cr = .Ok c → ∀ kr c', chain.Chain.recv_key c 0#u64 mp.index = ok (kr, c') →
      chain.Chain.into_pb c' ⦃ _ => True ⦄) :
    recv state msg ⦃ (result : core.result.Result Recv Error) =>
      match cr with
      | .Err e => result = .Err e
      | .Ok c =>
        ∃ kr c', chain.Chain.recv_key c 0#u64 mp.index = ok (kr, c') ∧
          match kr with
          | .Err e => result = .Err e
          | .Ok k => ∃ cpb bytes, chain.Chain.into_pb c' = ok cpb ∧
              encode_state_pb
                { version_negotiation := some vn, chain := some cpb,
                  inner := some (.V1 pb) } = ok bytes ∧
              result = .Ok { state := bytes, key := some k } ⦄ := by
  rw [recv_eq_greater state msg mp vn ch pb cr hpre hdec hge hgt hchain]
  cases cr with
  | Err e => simp
  | Ok c =>
    obtain ⟨⟨kr, c'⟩, hk, -⟩ := WP.spec_imp_exists (hkey c rfl)
    apply WP.exists_imp_spec
    cases kr with
    | Err e => exact ⟨_, by simp [hk], _, _, hk, rfl⟩
    | Ok k =>
      obtain ⟨cpb, hc, -⟩ := WP.spec_imp_exists (hpb c rfl _ _ hk)
      obtain ⟨bytes, hb, -⟩ := WP.spec_imp_exists (encode_state_pb_spec
        { version_negotiation := some vn, chain := some cpb, inner := some (.V1 pb) })
      exact ⟨_, by simp [hk, hc, hb], _, _, hk, cpb, bytes, hc, hb, rfl⟩

/-- **Spec theorem for `spqr.recv`** (`Ordering::Less`, downgrade to V0):
V1 state with pending negotiation and a V0 message.  An unknown `vn.direction` gives
`Err StateDecode`; a `chain_from` error is propagated; otherwise the downgraded state has
`inner = None`, so the result is the empty `Ok { state = [], key = None }`.
Requires that `into_pb` does not panic on the reconstructed chain. -/
theorem recv_spec_less_v0 (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (vn : proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (ch : Option proto.pq_ratchet.Chain) (pb : proto.pq_ratchet.V1State)
    (dr : core.result.Result proto.pq_ratchet.Direction prost.error.UnknownEnumValue)
    (cr : core.result.Result chain.Chain Error)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := some vn, chain := ch, inner := some (.V1 pb) }))
    (hge : ¬ mp.version < IScalar.hcast .U8 vn.min_version)
    (hv0 : mp.version.val = 0)
    (hdir : proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from
      vn.direction = ok dr)
    (hchain : chain_from ch (some vn) = ok cr)
    (hpb : ∀ c, cr = .Ok c → chain.Chain.into_pb c ⦃ _ => True ⦄) :
    recv state msg ⦃ (result : core.result.Result Recv Error) =>
      match dr with
      | .Err _ => result = .Err Error.StateDecode
      | .Ok _ =>
        match cr with
        | .Err e => result = .Err e
        | .Ok _ => result = recvV0Result ⦄ := by
  rw [recv_eq_less_v0 state msg mp vn ch pb dr cr hpre hdec hge hv0 hdir hchain]
  cases dr with
  | Err e => simp
  | Ok d =>
    cases cr with
    | Err e => simp
    | Ok c =>
      obtain ⟨cpb, hc, -⟩ := WP.spec_imp_exists (hpb c rfl)
      simp [hc]

/-- Postcondition of the same-version V1 receive path, relating the result to the
intermediate results of the Rust sub-calls (`?` propagation made explicit). -/
def recvV1Post (mp : MsgPreamble)
    (vn : Option proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (ch : Option proto.pq_ratchet.Chain) (pb : proto.pq_ratchet.V1State)
    (result : core.result.Result Recv Error) : Prop :=
  ∃ mr, v1.chunked.states.serialize.Message.deserialize mp.epoch mp.remaining = ok mr ∧
  match mr with
  | .Err e => result = .Err e
  | .Ok scka_msg =>
    ∃ sr, v1.chunked.states.serialize.States.from_pb pb = ok sr ∧
    match sr with
    | .Err e => result = .Err e
    | .Ok states =>
      ∃ rr, v1.chunked.states.States.recv states scka_msg = ok rr ∧
      match rr with
      | .Err e => result = .Err e
      | .Ok r =>
        ∃ msg_key_epoch, mp.epoch - 1#u64 = ok msg_key_epoch ∧
        ∃ cr, chain_from ch vn = ok cr ∧
        match cr with
        | .Err e => result = .Err e
        | .Ok c =>
          ∃ c1, (match r.key with
                 | none => ok c
                 | some es => chain.Chain.add_epoch c es) = ok c1 ∧
          ∃ kr c2, chain.Chain.recv_key c1 msg_key_epoch mp.index = ok (kr, c2) ∧
          match kr with
          | .Err e => result = .Err e
          | .Ok k =>
            ∃ vs cpb bytes,
              v1.chunked.states.serialize.States.into_pb r.state = ok vs ∧
              chain.Chain.into_pb c2 = ok cpb ∧
              encode_state_pb
                { version_negotiation := none, chain := some cpb, inner := some (.V1 vs) } =
                ok bytes ∧
              (k.val = [] → result = .Ok { state := bytes, key := none }) ∧
              (k.val ≠ [] → result = .Ok { state := bytes, key := some k })

/-- If `recvV1Model` does not panic, its result satisfies `recvV1Post`. -/
theorem recvV1Model_spec (mp : MsgPreamble)
    (vn : Option proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (ch : Option proto.pq_ratchet.Chain) (pb : proto.pq_ratchet.V1State)
    (hok : recvV1Model mp vn ch pb ⦃ _ => True ⦄) :
    recvV1Model mp vn ch pb ⦃ result => recvV1Post mp vn ch pb result ⦄ := by
  unfold recvV1Model at hok ⊢
  -- keep `recvV1Post` folded while rewriting the computation
  obtain ⟨mr, hmr, hok⟩ := WP.bind_spec_true hok
  simp only [hmr, bind_ok]
  cases mr with
  | Err e => rw [WP.spec_ok]; unfold recvV1Post; exact ⟨_, hmr, rfl⟩
  | Ok scka_msg =>
  obtain ⟨sr, hsr, hok⟩ := WP.bind_spec_true hok
  simp only [hsr, bind_ok]
  cases sr with
  | Err e => rw [WP.spec_ok]; unfold recvV1Post; exact ⟨_, hmr, _, hsr, rfl⟩
  | Ok states =>
  obtain ⟨rr, hrr, hok⟩ := WP.bind_spec_true hok
  simp only [hrr, bind_ok]
  cases rr with
  | Err e => rw [WP.spec_ok]; unfold recvV1Post; exact ⟨_, hmr, _, hsr, _, hrr, rfl⟩
  | Ok r =>
  obtain ⟨msg_key_epoch, hep, hok⟩ := WP.bind_spec_true hok
  obtain ⟨cr, hcr, hok⟩ := WP.bind_spec_true hok
  simp only [hep, hcr, bind_ok]
  cases cr with
  | Err e => rw [WP.spec_ok]; unfold recvV1Post; exact ⟨_, hmr, _, hsr, _, hrr, _, hep, _, hcr, rfl⟩
  | Ok c =>
  obtain ⟨c1, hc1, hok⟩ := WP.bind_spec_true hok
  obtain ⟨⟨kr, c2⟩, hk, hok⟩ := WP.bind_spec_true hok
  simp only [hc1, hk, bind_ok]
  cases kr with
  | Err e =>
    change (ok _) ⦃ _ ⦄
    rw [WP.spec_ok]; unfold recvV1Post
    exact ⟨_, hmr, _, hsr, _, hrr, _, hep, _, hcr, _, hc1, _, _, hk, rfl⟩
  | Ok k =>
  change (do
    let vs ← v1.chunked.states.serialize.States.into_pb r.state
    let cpb ← chain.Chain.into_pb c2
    let bytes ← encode_state_pb
      { version_negotiation := none, chain := some cpb, inner := some (.V1 vs) }
    let b ← alloc.vec.Vec.is_empty Global k
    if b then ok (core.result.Result.Ok (E := Error) (Recv.mk bytes none))
    else ok (core.result.Result.Ok (E := Error) (Recv.mk bytes (some k)))) ⦃ _ ⦄
  obtain ⟨vs, hvs, hok⟩ := WP.bind_spec_true hok
  obtain ⟨cpb, hcpb, hok⟩ := WP.bind_spec_true hok
  obtain ⟨bytes, hb, hok⟩ := WP.bind_spec_true hok
  simp only [hvs, hcpb, hb, bind_ok, alloc.vec.Vec.is_empty]
  by_cases hkv : k.val = []
  · simp only [List.isEmpty_iff, hkv, ↓reduceIte, WP.spec_ok]; unfold recvV1Post
    exact ⟨_, hmr, _, hsr, _, hrr, _, hep, _, hcr, _, hc1, _, _, hk, vs, cpb, bytes, hvs, hcpb,
      hb, fun _ => rfl, fun h => absurd hkv h⟩
  · simp only [List.isEmpty_iff, hkv, ↓reduceIte, WP.spec_ok]; unfold recvV1Post
    exact ⟨_, hmr, _, hsr, _, hrr, _, hep, _, hcr, _, hc1, _, _, hk, vs, cpb, bytes, hvs, hcpb,
      hb, fun h => absurd h hkv, fun _ => rfl⟩

/-- **Spec theorem for `spqr.recv`** (`Ordering::Equal`, V1, no negotiation):
V1 state without `version_negotiation` and a V1 message: the result satisfies
`recvV1Post mp none ch pb` — the chain is rebuilt from `st.chain` only, the message key is
`recv_key (msg.epoch - 1) msg.index`, the re-encoded state has `version_negotiation = None`,
and an empty key is reported as `None`.  Requires the V1 tail not to panic. -/
theorem recv_spec_equal_v1_no_negotiation (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (ch : Option proto.pq_ratchet.Chain) (pb : proto.pq_ratchet.V1State)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := none, chain := ch, inner := some (.V1 pb) }))
    (hv1 : mp.version.val = 1)
    (hok : recvV1Model mp none ch pb ⦃ _ => True ⦄) :
    recv state msg ⦃ (result : core.result.Result Recv Error) =>
      recvV1Post mp none ch pb result ⦄ := by
  rw [recv_eq_equal_v1_no_negotiation state msg mp ch pb hpre hdec hv1]
  exact recvV1Model_spec mp none ch pb hok

/-- **Spec theorem for `spqr.recv`** (`Ordering::Equal`, V1, still negotiating):
V1 state with pending `version_negotiation` and a V1 message at or above `vn.min_version`:
the result satisfies `recvV1Post mp (some vn) ch pb` — the chain may fall back to `vn` when
`st.chain = None`, and the re-encoded state **clears** the negotiation.
Requires the V1 tail not to panic. -/
theorem recv_spec_equal_v1_negotiating (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (vn : proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (ch : Option proto.pq_ratchet.Chain) (pb : proto.pq_ratchet.V1State)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := some vn, chain := ch, inner := some (.V1 pb) }))
    (hge : ¬ mp.version < IScalar.hcast .U8 vn.min_version)
    (hv1 : mp.version.val = 1)
    (hok : recvV1Model mp (some vn) ch pb ⦃ _ => True ⦄) :
    recv state msg ⦃ (result : core.result.Result Recv Error) =>
      recvV1Post mp (some vn) ch pb result ⦄ := by
  rw [recv_eq_equal_v1_negotiating state msg mp vn ch pb hpre hdec hge hv1]
  exact recvV1Model_spec mp (some vn) ch pb hok

/-! ## Total spec theorem -/

/-- Every result allowed by `recvV1Post` satisfies `recvPost`. -/
theorem recvPost_of_recvV1Post (mp : MsgPreamble)
    (vn : Option proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (ch : Option proto.pq_ratchet.Chain) (pb : proto.pq_ratchet.V1State)
    (result : core.result.Result Recv Error) (h : recvV1Post mp vn ch pb result) :
    recvPost result := by
  unfold recvV1Post at h
  obtain ⟨mr, -, h⟩ := h
  cases mr with
  | Err e => subst h; trivial
  | Ok _ =>
  obtain ⟨sr, -, h⟩ := h
  cases sr with
  | Err e => subst h; trivial
  | Ok _ =>
  obtain ⟨rr, -, h⟩ := h
  cases rr with
  | Err e => subst h; trivial
  | Ok r =>
  obtain ⟨_, -, cr, -, h⟩ := h
  cases cr with
  | Err e => subst h; trivial
  | Ok _ =>
  obtain ⟨_, -, kr, _, -, h⟩ := h
  cases kr with
  | Err e => subst h; trivial
  | Ok k =>
  obtain ⟨vs, cpb, bytes, -, -, hb, hnone, hsome⟩ := h
  by_cases hkv : k.val = []
  · rw [hnone hkv]
    exact Or.inr ⟨_, hb, ⟨cpb, rfl⟩, ⟨vs, rfl⟩, Or.inl ⟨rfl, fun _ h => by cases h⟩⟩
  · rw [hsome hkv]
    exact Or.inr ⟨_, hb, ⟨cpb, rfl⟩, ⟨vs, rfl⟩,
      Or.inl ⟨rfl, fun k' hk' => by cases hk'; exact hkv⟩⟩

/-- **Spec theorem for `spqr.recv`** (total):

Assuming `recv` does not panic, every result satisfies `recvPost`: a successful result is either
the empty V0 result `{ state = [], key = None }` or a re-encoded state with a chain and a V1
inner state, with `version_negotiation` cleared (same-version path; absent key ⇔ empty key) or
kept (newer remote version; key always present).  Application errors are passed through.

The no-panic premise is required because the sub-calls (`Chain::recv_key`, `Chain::into_pb`,
`States::recv`, …) have well-formedness preconditions that a raw decoded state does not
establish; see the per-path theorems for the exact result on each branch.

**Source**: spqr/src/lib.rs (lines 361:0-490:1) -/
@[step]
theorem recv_spec (state msg : alloc.vec.Vec U8) (hok : recv state msg ⦃ _ => True ⦄) :
    recv state msg ⦃ (result : core.result.Result Recv Error) => recvPost result ⦄ := by
  -- Peel the two leading `?` calls off the non-panic hypothesis.
  have hok' := hok
  unfold recv at hok'
  obtain ⟨pr, hpre, hok'⟩ := WP.bind_spec_true hok'
  cases pr with
  | Err e =>
    rw [recv_eq_msg_preamble_err state msg e hpre, WP.spec_ok]; trivial
  | Ok mp =>
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at hok'
  obtain ⟨dr, hdec, -⟩ := WP.bind_spec_true hok'
  cases dr with
  | Err e =>
    rw [recv_eq_decode_state_err state msg mp e hpre hdec, WP.spec_ok]; trivial
  | Ok st =>
  obtain ⟨vn, ch, inner⟩ := st
  rcases inner with _ | inner <;> (try obtain ⟨pb⟩ := inner) <;> rcases vn with _ | vn
  · -- V0, no negotiation
    rw [recv_eq_v0_no_negotiation state msg mp ch hpre hdec, WP.spec_ok]
    exact Or.inl rfl
  · -- V0, negotiating
    by_cases hlt : mp.version < IScalar.hcast .U8 vn.min_version
    · rw [recv_eq_minimum_version_negotiating state msg mp vn ch none hpre hdec hlt, WP.spec_ok]
      trivial
    · rw [recv_eq_v0_negotiating state msg mp vn ch hpre hdec hlt, WP.spec_ok]
      exact Or.inl rfl
  · -- V1, no negotiation
    rcases Nat.lt_trichotomy mp.version.val 1 with hlt | heq | hgt
    · rw [recv_eq_minimum_version_no_negotiation state msg mp ch pb hpre hdec hlt, WP.spec_ok]
      trivial
    · have h := recv_eq_equal_v1_no_negotiation state msg mp ch pb hpre hdec heq
      rw [h] at hok ⊢
      exact WP.spec_mono (recvV1Model_spec mp none ch pb hok)
        (fun r => recvPost_of_recvV1Post mp none ch pb r)
    · rw [recv_eq_version_mismatch state msg mp ch pb hpre hdec hgt, WP.spec_ok]; trivial
  · -- V1, negotiating
    by_cases hge : mp.version < IScalar.hcast .U8 vn.min_version
    · rw [recv_eq_minimum_version_negotiating state msg mp vn ch _ hpre hdec hge, WP.spec_ok]
      trivial
    rcases Nat.lt_trichotomy mp.version.val 1 with hlt | heq | hgt
    · -- downgrade to V0
      have hv0 : mp.version.val = 0 := by omega
      obtain ⟨dr, hdir, -⟩ := WP.spec_imp_exists
        (proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from_spec
          vn.direction)
      obtain ⟨cr, hchain, -⟩ := WP.spec_imp_exists (chain_from_spec ch (some vn))
      have h := recv_eq_less_v0 state msg mp vn ch pb dr cr hpre hdec hge hv0 hdir hchain
      rw [h] at hok ⊢
      cases dr with
      | Err _ => rw [WP.spec_ok]; trivial
      | Ok _ =>
      cases cr with
      | Err _ => rw [WP.spec_ok]; trivial
      | Ok c =>
      obtain ⟨cpb, hc, -⟩ := WP.bind_spec_true hok
      simp only [hc, bind_ok, WP.spec_ok, recvV0Result]
      exact Or.inl rfl
    · have h := recv_eq_equal_v1_negotiating state msg mp vn ch pb hpre hdec hge heq
      rw [h] at hok ⊢
      exact WP.spec_mono (recvV1Model_spec mp (some vn) ch pb hok)
        (fun r => recvPost_of_recvV1Post mp (some vn) ch pb r)
    · -- their version is newer
      obtain ⟨cr, hchain, -⟩ := WP.spec_imp_exists (chain_from_spec ch (some vn))
      have h := recv_eq_greater state msg mp vn ch pb cr hpre hdec hge hgt hchain
      rw [h] at hok ⊢
      cases cr with
      | Err _ => rw [WP.spec_ok]; trivial
      | Ok c =>
      obtain ⟨⟨kr, c'⟩, hk, hok⟩ := WP.bind_spec_true hok
      apply WP.exists_imp_spec
      cases kr with
      | Err e => exact ⟨.Err e, by simp [hk], trivial⟩
      | Ok k =>
      obtain ⟨cpb, hc, hok⟩ := WP.bind_spec_true hok
      obtain ⟨bytes, hb, -⟩ := WP.bind_spec_true hok
      refine ⟨.Ok { state := bytes, key := some k }, by simp [hk, hc, hb], ?_⟩
      exact Or.inr ⟨_, hb, ⟨cpb, rfl⟩, ⟨pb, rfl⟩, Or.inr ⟨vn, rfl, k, rfl⟩⟩

end spqr
