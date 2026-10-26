/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Lib.StatePb
public import Spqr.Specs.Lib.Recv.ChainWf
public import Spqr.Specs.Lib.MsgPreamble
public import Spqr.Specs.Lib.DecodeState
public import Spqr.Specs.Chain.Chain.RecvKey
import Spqr.Specs.Chain.Chain.IntoPb
import Spqr.Specs.V1.Chunked.States.Serialize.Message.Deserialize
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

The registered `@[step]` contract is the total `recv_spec`.  Its postcondition `recvPost` is
**input-relative**: it is stated in terms of the preamble `msg_preamble` parses from `msg` and
the state `decode_state` decodes from `state`, and on each branch names the exact result —
which error, which key (`recvKeyPost` at epoch `0` resp. `msg.epoch - 1`), and which re-encoded
state (as a `decodesTo` fact, the form `decode_state_spec` consumes on the next call).  The
per-path `recv_spec_<path>` theorems are the branches of `recvPost` restated as standalone
contracts; `recv_spec_v0` covers the empty-input case.

**Progress.**  `recv_spec` takes no hypothesis on `recv` itself.  The deque well-formedness
preconditions of `Chain::into_pb` / `Chain::recv_key` are discharged for every chain `recv`
builds (`chainDequeWf_of_chainFrom`, `chainDequeWf_of_recvKeyPost`); the remaining
preconditions are on the *inputs*:

* `hready` — the counter/bounds conditions of `Chain::recv_key` (`recvKeyReady`) at epoch
  `0` for the chain `chain_from` reconstructs (`Ordering::Greater` path);
* `recvV1ChainReady` — on the same-version `V1` path: `msg.epoch ≥ 1`, `Chain::add_epoch`
  is ready for the epoch secret `States::recv` emits, and `Chain::recv_key` is ready at
  `(msg.epoch - 1, msg.index)`;
* `recvV1StatesOk` — the three `States::*` sub-calls (`from_pb`, `recv`, `into_pb`) do not
  panic.  They have no registered specs yet (`Spqr/Specs/V1/Chunked/States/…`); once they
  exist this hypothesis can be discharged without touching the statement.

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
| all of the above                                  | `recv_spec` (postcondition `recvPost`)       |

**Source**: spqr/src/lib.rs (lines 361:0-490:1)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr

/-- The canonical V0 (disabled) receive result: empty state, no key. -/
def recvV0Result : core.result.Result Recv Error :=
  .Ok { state := alloc.vec.Vec.new U8, key := none }

/-- `state_version(st) as u8`: `0` without an inner state, `1` with one. -/
def currentVersionU8 (st : proto.pq_ratchet.PqRatchetState) : U8 :=
  match st.inner with
  | none => 0#u8
  | some _ => 1#u8

/-- `min_version` of the Rust negotiation check: `vn.min_version as u8` while negotiating,
the current version otherwise. -/
def minVersionU8 (st : proto.pq_ratchet.PqRatchetState) : U8 :=
  match st.version_negotiation with
  | none => currentVersionU8 st
  | some vn => IScalar.hcast .U8 vn.min_version

/-- Postcondition of the `Ordering::Greater` path (their version is newer than ours): the chain
is rebuilt via `chain_from st.chain (Some vn)`; on success the key is pulled from **epoch 0**
with `recv_key c 0 msg.index` (`recvKeyPost`), the updated chain is re-encoded, and the
persisted state **keeps** `version_negotiation = Some vn` and `inner = Some (V1 pb)`.  Errors of
`chain_from` / `recv_key` are returned verbatim. -/
def recvGreaterPost (mp : MsgPreamble)
    (vn : proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (ch : Option proto.pq_ratchet.Chain) (pb : proto.pq_ratchet.V1State)
    (result : core.result.Result Recv Error) : Prop :=
  ∃ cr, chainFrom ch (some vn) = ok cr ∧
  match cr with
  | .Err e => result = .Err e
  | .Ok c =>
    ∃ kr c', chain.recvKeyPost c 0#u64 mp.index kr c' ∧
      match kr with
      | .Err e => result = .Err e
      | .Ok k => ∃ r, result = .Ok r ∧ r.key = some k ∧
          decodesTo r.state
            { version_negotiation := some vn,
              chain := some (chain.Chain.FunctionalModels.intoPb c'),
              inner := some (.V1 pb) }

/-- Postcondition of the `Ordering::Less` path (downgrade to V0): an unknown `vn.direction`
gives `Err StateDecode`; a `chain_from st.chain (Some vn)` error is propagated; otherwise the
downgraded state has `inner = None`, so the result is the empty `Ok { state = [], key = None }`. -/
def recvLessPost (vn : proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (ch : Option proto.pq_ratchet.Chain)
    (result : core.result.Result Recv Error) : Prop :=
  match parseDirection vn with
  | none => result = .Err Error.StateDecode
  | some _ =>
    ∃ cr, chainFrom ch (some vn) = ok cr ∧
    match cr with
    | .Err e => result = .Err e
    | .Ok _ => result = recvV0Result

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
  rw [ite_eq_right hge]
  simp only [hv1, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_ok,
    core.cmp.impls.OrdU8.cmp, core.option.Option.as_ref]
  rw [ite_eq_right (by decide)]
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
The only precondition beyond the branch conditions is `recvKeyReady` for `(0, msg.index)` on
the reconstructed chain; deque well-formedness is derived from `chain_from`. -/
theorem recv_spec_greater (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (vn : proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (ch : Option proto.pq_ratchet.Chain) (pb : proto.pq_ratchet.V1State)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := some vn, chain := ch, inner := some (.V1 pb) }))
    (hge : ¬ mp.version < IScalar.hcast .U8 vn.min_version)
    (hgt : 1 < mp.version.val)
    (hready : ∀ c, chainFrom ch (some vn) = ok (.Ok c) → recvKeyReady c 0#u64 mp.index) :
    recv state msg ⦃ (result : core.result.Result Recv Error) =>
      recvGreaterPost mp vn ch pb result ⦄ := by
  obtain ⟨cr, hchain, hcr⟩ := WP.spec_imp_exists (chain_from_spec ch (some vn))
  rw [recv_eq_greater state msg mp vn ch pb cr hpre hdec hge hgt hchain]
  unfold recvGreaterPost
  cases cr with
  | Err e => rw [WP.spec_ok]; exact ⟨_, hcr, rfl⟩
  | Ok c =>
    have hwf := chainDequeWf_of_chainFrom ch (some vn) c hcr
    obtain ⟨hfits, htarget⟩ := hready c hcr
    obtain ⟨⟨kr, c'⟩, hk, hkpost⟩ :=
      WP.spec_imp_exists (chain.Chain.recv_key_spec c 0#u64 mp.index hfits hwf htarget)
    dsimp only
    rw [hk, bind_ok]
    cases kr with
    | Err e => exact WP.exists_imp_spec ⟨_, rfl, _, hcr, _, _, hkpost, rfl⟩
    | Ok k =>
      have hwf' := chainDequeWf_of_recvKeyPost c c' _ _ _ hwf hkpost
      obtain ⟨cpb, hc, rfl⟩ := WP.spec_imp_exists (chain.Chain.into_pb_spec c' hwf')
      obtain ⟨bytes, hb, hdt⟩ := WP.spec_imp_exists (encode_state_pb_spec
        { version_negotiation := some vn,
          chain := some (chain.Chain.FunctionalModels.intoPb c'), inner := some (.V1 pb) })
      change (do
        let cpb ← chain.Chain.into_pb c'
        let bytes ← encode_state_pb
          { version_negotiation := some vn, chain := some cpb, inner := some (.V1 pb) }
        ok (core.result.Result.Ok (E := Error) (Recv.mk bytes (some k)))) ⦃ _ ⦄
      rw [hc, bind_ok, hb, bind_ok]
      exact WP.exists_imp_spec ⟨_, rfl, _, hcr, _, _, hkpost, _, rfl, rfl, hdt⟩

/-- **Spec theorem for `spqr.recv`** (`Ordering::Less`, downgrade to V0):
V1 state with pending negotiation and a V0 message.  An unknown `vn.direction` gives
`Err StateDecode`; a `chain_from` error is propagated; otherwise the downgraded state has
`inner = None`, so the result is the empty `Ok { state = [], key = None }`.  No precondition
beyond the branch conditions: deque well-formedness is derived from `chain_from`. -/
theorem recv_spec_less_v0 (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (vn : proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (ch : Option proto.pq_ratchet.Chain) (pb : proto.pq_ratchet.V1State)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := some vn, chain := ch, inner := some (.V1 pb) }))
    (hge : ¬ mp.version < IScalar.hcast .U8 vn.min_version)
    (hv0 : mp.version.val = 0) :
    recv state msg ⦃ (result : core.result.Result Recv Error) =>
      recvLessPost vn ch result ⦄ := by
  obtain ⟨dr, hdir, hdr⟩ := WP.spec_imp_exists
    (proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from_spec
      vn.direction)
  obtain ⟨cr, hchain, hcr⟩ := WP.spec_imp_exists (chain_from_spec ch (some vn))
  rw [recv_eq_less_v0 state msg mp vn ch pb dr cr hpre hdec hge hv0 hdir hchain]
  -- `dr` is `Ok` exactly when `parseDirection vn` is `some`.
  unfold recvLessPost
  cases dr with
  | Err e =>
    have hpd : parseDirection vn = none := by
      unfold parseDirection
      split <;> simp_all
    rw [hpd]
    exact WP.exists_imp_spec ⟨_, rfl, rfl⟩
  | Ok d =>
    have hpd : parseDirection vn = some d := by
      unfold parseDirection
      split <;> simp_all
    rw [hpd]
    cases cr with
    | Err e => rw [WP.spec_ok]; exact ⟨_, hcr, rfl⟩
    | Ok c =>
      have hwf := chainDequeWf_of_chainFrom ch (some vn) c hcr
      obtain ⟨cpb, hc, -⟩ := WP.spec_imp_exists (chain.Chain.into_pb_spec c hwf)
      simp only [hc, bind_ok, WP.spec_ok]
      exact ⟨_, hcr, trivial⟩

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
        ∃ msg_key_epoch : U64, msg_key_epoch.val = mp.epoch.val - 1 ∧
        ∃ cr, chainFrom ch vn = ok cr ∧
        match cr with
        | .Err e => result = .Err e
        | .Ok c =>
          ∃ c1, (match r.key with
                 | none => ok c
                 | some es => chain.Chain.add_epoch c es) = ok c1 ∧
          ∃ kr c2, chain.recvKeyPost c1 msg_key_epoch mp.index kr c2 ∧
          match kr with
          | .Err e => result = .Err e
          | .Ok k =>
            ∃ vs bytes,
              v1.chunked.states.serialize.States.into_pb r.state = ok vs ∧
              decodesTo bytes
                { version_negotiation := none,
                  chain := some (chain.Chain.FunctionalModels.intoPb c2),
                  inner := some (.V1 vs) } ∧
              (k.val = [] → result = .Ok { state := bytes, key := none }) ∧
              (k.val ≠ [] → result = .Ok { state := bytes, key := some k })

/-- The no-panic obligations of the same-version V1 tail that are **not** yet discharged by
registered specs: the three `States::*` sub-calls.  Everything chain-side (`chain_from`,
`add_epoch`, `recv_key`, `into_pb`, `encode_state_pb`) is covered by `recvV1ChainReady`. -/
def recvV1StatesOk (mp : MsgPreamble) (pb : proto.pq_ratchet.V1State) : Prop :=
  (∀ scka_msg,
    v1.chunked.states.serialize.Message.deserialize mp.epoch mp.remaining = ok (.Ok scka_msg) →
    v1.chunked.states.serialize.States.from_pb pb ⦃ _ => True ⦄ ∧
    ∀ states, v1.chunked.states.serialize.States.from_pb pb = ok (.Ok states) →
      v1.chunked.states.States.recv states scka_msg ⦃ _ => True ⦄ ∧
      ∀ r, v1.chunked.states.States.recv states scka_msg = ok (.Ok r) →
        v1.chunked.states.serialize.States.into_pb r.state ⦃ _ => True ⦄)

/-- The input-dependent chain preconditions of the same-version V1 tail: for the chain `c`
that `chain_from` rebuilds and the epoch secret `es` (if any) that `States::recv` emits,
`add_epoch` is ready, and `recv_key` is ready at `(msg.epoch - 1, msg.index)` on the chain
after the optional `add_epoch`. -/
def recvV1ChainReady (mp : MsgPreamble)
    (vn : Option proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (ch : Option proto.pq_ratchet.Chain) (pb : proto.pq_ratchet.V1State) : Prop :=
  1 ≤ mp.epoch.val ∧
  mp.remaining.length + 32 ≤ Usize.max ∧
  ∀ c, chainFrom ch vn = ok (.Ok c) →
    ∀ scka_msg states r,
      v1.chunked.states.serialize.Message.deserialize mp.epoch mp.remaining = ok (.Ok scka_msg) →
      v1.chunked.states.serialize.States.from_pb pb = ok (.Ok states) →
      v1.chunked.states.States.recv states scka_msg = ok (.Ok r) →
      (∀ es, r.key = some es → addEpochReady c es) ∧
      ∀ c1, (match r.key with
             | none => ok c
             | some es => chain.Chain.add_epoch c es) = ok c1 →
        ∀ e : U64, e.val = mp.epoch.val - 1 → recvKeyReady c1 e mp.index

/-- `encode_state_pb st = ok bytes` already carries `decodesTo bytes st`
(from the axiom `encode_state_pb_spec`). -/
theorem decodesTo_of_encode_state_pb (st : proto.pq_ratchet.PqRatchetState)
    (bytes : alloc.vec.Vec U8) (h : encode_state_pb st = ok bytes) : decodesTo bytes st := by
  obtain ⟨bytes', h', hdt⟩ := WP.spec_imp_exists (encode_state_pb_spec st)
  obtain rfl := Result.ok_injective (h'.symm.trans h)
  exact hdt

/-- Under `recvV1StatesOk` (no-panic of the three `States::*` sub-calls) and
`recvV1ChainReady` (chain-side readiness), `recvV1Model` does not panic and its result
satisfies `recvV1Post`.  Deque well-formedness of every intermediate chain is derived. -/
theorem recvV1Model_spec (mp : MsgPreamble)
    (vn : Option proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (ch : Option proto.pq_ratchet.Chain) (pb : proto.pq_ratchet.V1State)
    (hst : recvV1StatesOk mp pb) (hch : recvV1ChainReady mp vn ch pb) :
    recvV1Model mp vn ch pb ⦃ result => recvV1Post mp vn ch pb result ⦄ := by
  obtain ⟨hep1, hrem, hch⟩ := hch
  unfold recvV1Model
  obtain ⟨mr, hmr, -⟩ := WP.spec_imp_exists
    (v1.chunked.states.serialize.Message.deserialize_spec mp.epoch mp.remaining hrem)
  simp only [hmr, bind_ok]
  cases mr with
  | Err e => rw [WP.spec_ok]; unfold recvV1Post; exact ⟨_, hmr, rfl⟩
  | Ok scka_msg =>
  obtain ⟨hfp, hst⟩ := hst scka_msg hmr
  obtain ⟨sr, hsr, -⟩ := WP.spec_imp_exists hfp
  simp only [hsr, bind_ok]
  cases sr with
  | Err e => rw [WP.spec_ok]; unfold recvV1Post; exact ⟨_, hmr, _, hsr, rfl⟩
  | Ok states =>
  obtain ⟨hrc, hst⟩ := hst states hsr
  obtain ⟨rr, hrr, -⟩ := WP.spec_imp_exists hrc
  simp only [hrr, bind_ok]
  cases rr with
  | Err e => rw [WP.spec_ok]; unfold recvV1Post; exact ⟨_, hmr, _, hsr, _, hrr, rfl⟩
  | Ok r =>
  have hip := hst r hrr
  obtain ⟨msg_key_epoch, hep, hepv, -⟩ := WP.spec_imp_exists
    (U64.sub_spec (x := mp.epoch) (y := 1#u64) (by simp; omega))
  obtain ⟨cr, hchain, hcr⟩ := WP.spec_imp_exists (chain_from_spec ch vn)
  simp only [hep, hchain, bind_ok]
  cases cr with
  | Err e =>
    rw [WP.spec_ok]; unfold recvV1Post
    exact ⟨_, hmr, _, hsr, _, hrr, _, hepv, _, hcr, rfl⟩
  | Ok c =>
  obtain ⟨hae, hready⟩ := hch c hcr scka_msg states r hmr hsr hrr
  have hwf := chainDequeWf_of_chainFrom ch vn c hcr
  -- the optional `add_epoch`
  have hc1 : ∃ c1, (match r.key with
      | none => ok c
      | some es => chain.Chain.add_epoch c es) = ok c1 ∧ chainDequeWf c1 := by
    cases hk : r.key with
    | none => exact ⟨c, rfl, hwf⟩
    | some es =>
      obtain ⟨c1, h1, -⟩ := WP.spec_imp_exists (chain.Chain.add_epoch_spec c es (hae es hk).1
        (by unfold chainDequeWf at hwf; omega) (hae es hk).2)
      exact ⟨c1, h1, chainDequeWf_of_addEpoch c c1 es hwf (hae es hk) h1⟩
  obtain ⟨c1, hc1, hwf1⟩ := hc1
  simp only [hc1, bind_ok]
  obtain ⟨hfits, htarget⟩ := hready c1 hc1 msg_key_epoch hepv
  obtain ⟨⟨kr, c2⟩, hk, hkpost⟩ := WP.spec_imp_exists
    (chain.Chain.recv_key_spec c1 msg_key_epoch mp.index hfits hwf1 htarget)
  simp only [hk, bind_ok]
  cases kr with
  | Err e =>
    change (ok _) ⦃ _ ⦄
    rw [WP.spec_ok]; unfold recvV1Post
    exact ⟨_, hmr, _, hsr, _, hrr, _, hepv, _, hcr, _, hc1, _, _, hkpost, rfl⟩
  | Ok k =>
  change (do
    let vs ← v1.chunked.states.serialize.States.into_pb r.state
    let cpb ← chain.Chain.into_pb c2
    let bytes ← encode_state_pb
      { version_negotiation := none, chain := some cpb, inner := some (.V1 vs) }
    let b ← alloc.vec.Vec.is_empty Global k
    if b then ok (core.result.Result.Ok (E := Error) (Recv.mk bytes none))
    else ok (core.result.Result.Ok (E := Error) (Recv.mk bytes (some k)))) ⦃ _ ⦄
  obtain ⟨vs, hvs, -⟩ := WP.spec_imp_exists hip
  have hwf2 := chainDequeWf_of_recvKeyPost c1 c2 _ _ _ hwf1 hkpost
  obtain ⟨cpb, hcpb, rfl⟩ := WP.spec_imp_exists (chain.Chain.into_pb_spec c2 hwf2)
  obtain ⟨bytes, hb, hdt⟩ := WP.spec_imp_exists (encode_state_pb_spec
    { version_negotiation := none,
      chain := some (chain.Chain.FunctionalModels.intoPb c2), inner := some (.V1 vs) })
  simp only [hvs, hcpb, hb, bind_ok, alloc.vec.Vec.is_empty]
  by_cases hkv : k.val = []
  · simp only [List.isEmpty_iff, hkv, ↓reduceIte, WP.spec_ok]; unfold recvV1Post
    exact ⟨_, hmr, _, hsr, _, hrr, _, hepv, _, hcr, _, hc1, _, _, hkpost, vs, bytes, hvs,
      hdt, fun _ => rfl, fun h => absurd hkv h⟩
  · simp only [List.isEmpty_iff, hkv, ↓reduceIte, WP.spec_ok]; unfold recvV1Post
    exact ⟨_, hmr, _, hsr, _, hrr, _, hepv, _, hcr, _, hc1, _, _, hkpost, vs, bytes, hvs,
      hdt, fun h => absurd h hkv, fun _ => rfl⟩

/-- **Spec theorem for `spqr.recv`** (`Ordering::Equal`, V1, no negotiation):
V1 state without `version_negotiation` and a V1 message: the result satisfies
`recvV1Post mp none ch pb` — the chain is rebuilt from `st.chain` only, the message key is
`recv_key (msg.epoch - 1) msg.index`, the re-encoded state has `version_negotiation = None`,
and an empty key is reported as `None`.  Requires `recvV1StatesOk` (no-panic of the
`States::*` sub-calls) and `recvV1ChainReady` (chain-side readiness). -/
theorem recv_spec_equal_v1_no_negotiation (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (ch : Option proto.pq_ratchet.Chain) (pb : proto.pq_ratchet.V1State)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := none, chain := ch, inner := some (.V1 pb) }))
    (hv1 : mp.version.val = 1)
    (hst : recvV1StatesOk mp pb) (hch : recvV1ChainReady mp none ch pb) :
    recv state msg ⦃ (result : core.result.Result Recv Error) =>
      recvV1Post mp none ch pb result ⦄ := by
  rw [recv_eq_equal_v1_no_negotiation state msg mp ch pb hpre hdec hv1]
  exact recvV1Model_spec mp none ch pb hst hch

/-- **Spec theorem for `spqr.recv`** (`Ordering::Equal`, V1, still negotiating):
V1 state with pending `version_negotiation` and a V1 message at or above `vn.min_version`:
the result satisfies `recvV1Post mp (some vn) ch pb` — the chain may fall back to `vn` when
`st.chain = None`, and the re-encoded state **clears** the negotiation.
Requires `recvV1StatesOk` and `recvV1ChainReady`. -/
theorem recv_spec_equal_v1_negotiating (state msg : alloc.vec.Vec U8)
    (mp : MsgPreamble) (vn : proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (ch : Option proto.pq_ratchet.Chain) (pb : proto.pq_ratchet.V1State)
    (hpre : msg_preamble msg = ok (.Ok mp))
    (hdec : decode_state state =
      ok (.Ok { version_negotiation := some vn, chain := ch, inner := some (.V1 pb) }))
    (hge : ¬ mp.version < IScalar.hcast .U8 vn.min_version)
    (hv1 : mp.version.val = 1)
    (hst : recvV1StatesOk mp pb) (hch : recvV1ChainReady mp (some vn) ch pb) :
    recv state msg ⦃ (result : core.result.Result Recv Error) =>
      recvV1Post mp (some vn) ch pb result ⦄ := by
  rw [recv_eq_equal_v1_negotiating state msg mp vn ch pb hpre hdec hge hv1]
  exact recvV1Model_spec mp (some vn) ch pb hst hch


/-! ## Total spec theorem -/

/-- Postcondition of `recv` **after** `msg_preamble` and `decode_state` have both succeeded,
indexed by the parsed preamble `mp` and the decoded state `st`.  It follows the Rust control
flow exactly:

* `mp.version < min_version` → `Err MinimumVersion`;
* otherwise, with `inner = None` (current version `0`) → the empty `recvV0Result`;
* otherwise (`inner = Some (V1 pb)`, current version `1`) by `compare mp.version 1`:
  - `.gt`, `vn = None` → `Err VersionMismatch`; `vn = Some` → `recvGreaterPost`;
  - `.lt` (so `mp.version = 0`; `vn = Some` is forced by the min-version check) →
    `recvLessPost`;
  - `.eq` → `recvV1Post` (chain from `st.chain` with `vn` fallback, key at
    `msg.epoch - 1`, negotiation cleared). -/
def recvDecodedPost (mp : MsgPreamble) (st : proto.pq_ratchet.PqRatchetState)
    (result : core.result.Result Recv Error) : Prop :=
  if mp.version < minVersionU8 st then result = .Err Error.MinimumVersion
  else
    match st.inner with
    | none => result = recvV0Result
    | some (.V1 pb) =>
      match compare mp.version.val 1, st.version_negotiation with
      | .gt, none => result = .Err Error.VersionMismatch
      | .gt, some vn => recvGreaterPost mp vn st.chain pb result
      | .lt, none => False  -- unreachable: `mp.version < 1 = min_version`
      | .lt, some vn => recvLessPost vn st.chain result
      | .eq, vn => recvV1Post mp vn st.chain pb result

/-- **Total postcondition for `spqr.recv`**, relative to the inputs: an `Err` of
`msg_preamble` or `decode_state` is returned unchanged, and once both succeed the result is
`recvDecodedPost` for the parsed preamble and decoded state. -/
def recvPost (state msg : alloc.vec.Vec U8) (result : core.result.Result Recv Error) : Prop :=
  (∀ e, msg_preamble msg = ok (.Err e) → result = .Err e) ∧
  (∀ mp e, msg_preamble msg = ok (.Ok mp) → decode_state state = ok (.Err e) →
    result = .Err e) ∧
  (∀ mp st, msg_preamble msg = ok (.Ok mp) → decode_state state = ok (.Ok st) →
    recvDecodedPost mp st result)

/-- Inputs under which every sub-call of `recv` is known not to panic:

* `Ordering::Greater`: `recv_key (0, msg.index)` is ready on the chain `chain_from`
  reconstructs from `st.chain`/`vn`;
* `Ordering::Equal`: the three `States::*` sub-calls do not panic (`recvV1StatesOk` — they
  have no registered specs yet) and the chain side is ready (`recvV1ChainReady`: `msg.epoch ≥ 1`,
  `add_epoch` ready for the emitted epoch secret, `recv_key` ready at
  `(msg.epoch - 1, msg.index)`). -/
def recvInputsOk (state msg : alloc.vec.Vec U8) : Prop :=
  ∀ mp st, msg_preamble msg = ok (.Ok mp) → decode_state state = ok (.Ok st) →
    ∀ pb, st.inner = some (.V1 pb) →
      (∀ vn, st.version_negotiation = some vn → 1 < mp.version.val →
        ∀ c, chainFrom st.chain (some vn) = ok (.Ok c) → recvKeyReady c 0#u64 mp.index) ∧
      (mp.version.val = 1 →
        recvV1StatesOk mp pb ∧ recvV1ChainReady mp st.version_negotiation st.chain pb)

/-- **Spec theorem for `spqr.recv`** (total):

Under `recvInputsOk state msg` — preconditions on the *inputs* only — `recv` does not panic
and its result satisfies `recvPost state msg`: errors of `msg_preamble`/`decode_state` are
passed through, and otherwise `recvDecodedPost` names the exact result of the branch the
parsed preamble and decoded state select (which error; the key from `recv_key` at epoch `0`
resp. `msg.epoch - 1`; the re-encoded state as a `decodesTo` fact with `version_negotiation`
kept resp. cleared and `inner` preserved resp. updated).

**Source**: spqr/src/lib.rs (lines 361:0-490:1) -/
@[step]
theorem recv_spec (state msg : alloc.vec.Vec U8) (hin : recvInputsOk state msg) :
    recv state msg ⦃ (result : core.result.Result Recv Error) => recvPost state msg result ⦄ := by
  obtain ⟨pr, hpre, -⟩ := WP.spec_imp_exists (msg_preamble_spec msg)
  cases pr with
  | Err e =>
    rw [recv_eq_msg_preamble_err state msg e hpre, WP.spec_ok]
    refine ⟨fun e' h => ?_, fun _ _ h => ?_, fun _ _ h => ?_⟩
    · cases Result.ok_injective (hpre.symm.trans h); rfl
    · cases Result.ok_injective (hpre.symm.trans h)
    · cases Result.ok_injective (hpre.symm.trans h)
  | Ok mp =>
  obtain ⟨dr, hdec, -⟩ := WP.spec_imp_exists (decode_state_spec state)
  -- Every branch below only has to establish `recvDecodedPost mp st result`.
  have hpost : ∀ (result : core.result.Result Recv Error),
      (∀ st, dr = .Ok st → recvDecodedPost mp st result) →
      (∀ e, dr = .Err e → result = .Err e) → recvPost state msg result := by
    intro result hok herr
    refine ⟨fun _ h => ?_, fun mp' e h h' => ?_, fun mp' st h h' => ?_⟩
    · cases Result.ok_injective (hpre.symm.trans h)
    · cases Result.ok_injective (hpre.symm.trans h)
      exact herr e (Result.ok_injective (hdec.symm.trans h'))
    · cases Result.ok_injective (hpre.symm.trans h)
      exact hok st (Result.ok_injective (hdec.symm.trans h'))
  cases dr with
  | Err e =>
    rw [recv_eq_decode_state_err state msg mp e hpre hdec, WP.spec_ok]
    exact hpost _ (fun _ h => by cases h) (fun _ h => by cases h; rfl)
  | Ok st =>
  refine WP.spec_mono ?_ (fun r hr => hpost r (fun st' h => by cases h; exact hr)
    (fun _ h => by cases h))
  obtain ⟨vn, ch, inner⟩ := st
  have hin := hin mp _ hpre hdec
  rcases inner with _ | inner <;> (try obtain ⟨pb⟩ := inner) <;> rcases vn with _ | vn
  · -- V0, no negotiation: `min_version = 0`, nothing is below it
    rw [recv_eq_v0_no_negotiation state msg mp ch hpre hdec, WP.spec_ok]
    unfold recvDecodedPost minVersionU8 currentVersionU8
    simp
  · -- V0, negotiating
    unfold recvDecodedPost minVersionU8
    simp only
    by_cases hlt : mp.version < IScalar.hcast .U8 vn.min_version
    · rw [recv_eq_minimum_version_negotiating state msg mp vn ch none hpre hdec hlt, WP.spec_ok]
      simp [hlt]
    · rw [recv_eq_v0_negotiating state msg mp vn ch hpre hdec hlt, WP.spec_ok]
      simp [hlt]
  · -- V1, no negotiation: `min_version = 1`
    obtain ⟨-, hv1⟩ := hin pb rfl
    unfold recvDecodedPost minVersionU8 currentVersionU8
    simp only [UScalar.lt_equiv]
    rcases Nat.lt_trichotomy mp.version.val 1 with hlt | heq | hgt
    · rw [recv_eq_minimum_version_no_negotiation state msg mp ch pb hpre hdec hlt, WP.spec_ok]
      simp [hlt]
    · rw [recv_eq_equal_v1_no_negotiation state msg mp ch pb hpre hdec heq]
      refine WP.spec_mono (recvV1Model_spec mp none ch pb (hv1 heq).1 (hv1 heq).2)
        (fun r hr => ?_)
      simp [heq, hr]
    · rw [recv_eq_version_mismatch state msg mp ch pb hpre hdec hgt, WP.spec_ok]
      simp [Nat.compare_eq_gt.mpr hgt, show ¬ mp.version.val < 1 by omega]
  · -- V1, negotiating
    obtain ⟨hready, hv1⟩ := hin pb rfl
    unfold recvDecodedPost minVersionU8
    simp only
    by_cases hge : mp.version < IScalar.hcast .U8 vn.min_version
    · rw [recv_eq_minimum_version_negotiating state msg mp vn ch _ hpre hdec hge, WP.spec_ok]
      simp [hge]
    simp only [hge, ↓reduceIte]
    rcases Nat.lt_trichotomy mp.version.val 1 with hlt | heq | hgt
    · -- downgrade to V0
      have hv0 : mp.version.val = 0 := by omega
      refine WP.spec_mono (recv_spec_less_v0 state msg mp vn ch pb hpre hdec hge hv0)
        (fun r hr => ?_)
      simp [Nat.compare_eq_lt.mpr hlt, hr]
    · rw [recv_eq_equal_v1_negotiating state msg mp vn ch pb hpre hdec hge heq]
      refine WP.spec_mono (recvV1Model_spec mp (some vn) ch pb (hv1 heq).1 (hv1 heq).2)
        (fun r hr => ?_)
      simp [heq, hr]
    · -- their version is newer
      refine WP.spec_mono
        (recv_spec_greater state msg mp vn ch pb hpre hdec hge hgt (hready vn rfl hgt))
        (fun r hr => ?_)
      simp [Nat.compare_eq_gt.mpr hgt, hr]

end spqr

