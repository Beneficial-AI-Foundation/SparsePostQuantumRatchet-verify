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
/-!
# Spec theorem for `spqr::send`

`send` is the sending half of the public SPQR API. Given the serialised ratchet state and a
random number generator it

  1. decodes the state with `decode_state` and returns an empty `Send` if the decoded state has no
     `inner` field, i.e. when the post-quantum ratchet is disabled (version V0);
  2. otherwise deserialises the V1 inner state with `States::from_pb` and runs one step of the
     ML-KEM Braid state machine, `States::send`, which outputs a message, the new inner state and
     possibly a fresh epoch secret;
  3. selects the chain: the stored one (`Chain::from_pb`) if there is one; otherwise
     `Err ChainNotAvailable` without a version negotiation, no chain if `min_version <= 0`, and
     a fresh one from the version negotiation (`chain_from_version_negotiation`) if
     `min_version > 0`;
  4. with a chain, mixes the epoch secret (if any) in with `Chain::add_epoch`, derives the message
     key for epoch `msg.epoch - 1` with `Chain::send_key` and serialises the chain; without a
     chain the ratchet index is `0` and there is no key;
  5. serialises the message and re-encodes the state with `encode_state_pb` (new inner state, new
     chain if any, version negotiation unchanged).

`send_spec` is a total correctness statement under a single hypothesis, `SendAssumptions`, which
covers the callees without a specification and the facts that need an invariant on the ratchet
state. Every other callee is covered by its spec theorem or, for `encode_state_pb`, the axiom
`encode_state_pb_spec`. The deque well-formedness that the chain specifications demand is proved,
not assumed.

**Source**: spqr/src/lib.rs (lines 271:0-331:1)
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr

open v1.chunked v1.chunked.states
open chain.Chain.FunctionalModels (fromPb intoPb)

/-! ## What `send` assumes -/

/-- Everything `send_spec` assumes, localised to the values `send` reaches, so each item is vacuous
on the paths that do not reach it:

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
        -- Without a chain (none stored, `min_version <= 0`): the `assert!` in `send` (no epoch
        -- secret), then `States::into_pb`.
        ((st.chain = none ∧ ∃ vn ∈ st.version_negotiation, vn.min_version.val ≤ 0) →
          ss.key = none ∧ serialize.States.into_pb ss.state ⦃ _ => True ⦄) ∧
        -- The chain selection yields `.Ok c`: `fromPb` of the stored chain, or, when none is stored
        -- and `min_version > 0`, `chainFromVersionNegotiation`.
        ∀ c : chain.Chain, (∃ cpb ∈ st.chain, fromPb cpb = .Ok c) ∨
            (st.chain = none ∧ ∃ vn ∈ st.version_negotiation, 0 < vn.min_version.val ∧
              chainFromVersionNegotiation vn = ok (.Ok c)) →
          -- `msg.epoch - 1` does not underflow: the translation panics there, as debug Rust
          -- does (release Rust wraps).
          0 < ss.msg.epoch.val ∧
          -- `add_epoch_spec`: the epoch secret is for the epoch after the current one (the
          -- `assume!` of `Chain::add_epoch`), and the deque buffer can grow by one.
          (∀ k ∈ ss.key,
            k.epoch.val = c.current_epoch.val + 1 ∧ c.links.buf.val.length < Usize.max) ∧
          -- `c₁` is `c` with the epoch secret, if any, mixed in by `Chain::add_epoch`.
          ∀ c₁, ss.key.elim (ok c) c.add_epoch = ok c₁ → ∀ ep : U64, ep.val + 1 = ss.msg.epoch.val →
            -- `send_key_spec`: the epoch distance fits in a `usize` (the cast in
            -- `Chain::epoch_idx`), and the target slot holds a 32-byte send key whose counter can
            -- still advance (the last `assume!` of `Chain::send_key`).
            (c₁.send_epoch.val ≤ ep.val → ep.val ≤ c₁.current_epoch.val →
              c₁.current_epoch.val - ep.val ≤ Usize.max) ∧
            (c₁.send_epoch.val ≤ ep.val → ep.val ≤ c₁.current_epoch.val →
              c₁.current_epoch.val - ep.val < c₁.links.length.val →
              ∀ ce ∈ c₁.links.buf.val[c₁.links.head.val + chain.sendKeyIdx c₁ ep]?,
                ce.send.next.val.length = 32 ∧ ce.send.ctr.val < U32.max) ∧
            -- `States::into_pb`, which `send` calls once `send_key` has succeeded.
            ∀ i mk c₂, c₁.send_key ep = ok (.Ok (i, mk), c₂) →
              serialize.States.into_pb ss.state ⦃ _ => True ⦄

/-! ## What `send` returns after `States::send` -/

/-- The outcome `res` of `send` (`result.1` in `send_spec`) once `States::send` has produced `ss`
from the decoded state `st`, with one clause per way the chain selection can go:

- no stored chain and no version negotiation: `Err ChainNotAvailable`;
- no chain (none stored, `min_version <= 0`): `Ok`, with the message serialised at ratchet index
  `0` and no message key;
- a chain selection with outcome `sel`: its error, or, for a chain `c`, the epoch secret `ss.key`
  (if any) is mixed in with `add_epoch` and `send_key` ratchets the chain into `c₂`; then `res`
  is the error of `send_key`, or `Ok` with the message serialised at the ratchet index `i` and
  the message key `mk` that `send_key` returned.

On `Ok r` the state bytes `r.state` decode to `st` with the new inner state and, with a chain, the
new chain `c₂`; the version negotiation is unchanged. -/
def SendAfterStatesPost (st : proto.pq_ratchet.PqRatchetState) (ss : states.Send)
    (res : core.result.Result Send Error) : Prop :=
  ((st.chain = none ∧ st.version_negotiation = none) → res = .Err .ChainNotAvailable) ∧
  ((st.chain = none ∧ ∃ vn ∈ st.version_negotiation, vn.min_version.val ≤ 0) →
    ∃ r vs, res = .Ok r ∧ serialize.States.into_pb ss.state = ok vs ∧
      decodesTo r.state { st with inner := some (.V1 vs) } ∧
      r.msg.val.map UScalar.val = serialize.messageBytes ss.msg 0 ∧ r.key = none) ∧
  -- The chain selection yields `sel`: `fromPb` of the stored chain, or, when none is stored and
  -- `min_version > 0`, `chainFromVersionNegotiation`.
  ∀ sel, (∃ cpb ∈ st.chain, fromPb cpb = sel) ∨
      (st.chain = none ∧ ∃ vn ∈ st.version_negotiation, 0 < vn.min_version.val ∧
        chainFromVersionNegotiation vn = ok sel) →
    match sel with
    | .Err e => res = .Err e
    | .Ok c =>
      ∃ c₁ ep sk c₂, ss.key.elim (ok c) c.add_epoch = ok c₁ ∧ ep.val + 1 = ss.msg.epoch.val ∧
        c₁.send_key ep = ok (sk, c₂) ∧ chain.sendKeyPost c₁ ep sk c₂ ∧
        match sk with
        | .Err e => res = .Err e
        | .Ok (i, mk) =>
          ∃ r vs, res = .Ok r ∧ serialize.States.into_pb ss.state = ok vs ∧
            decodesTo r.state { st with chain := some (intoPb c₂), inner := some (.V1 vs) } ∧
            r.msg.val.map UScalar.val = serialize.messageBytes ss.msg i.val ∧ r.key = some mk

/-! ## Spec theorem -/

/-- **Spec theorem for `spqr.send`**:

Under `SendAssumptions`, `send` never panics and returns a pair `result`, fixed by the stages it
passes through on `state`:

- `decode_state` fails with `e`: `(Err e, rng)` (`e` is `StateDecode` by `decode_state_spec`).
- The decoded state has no `inner` (the ratchet is disabled): `Ok` with empty state bytes, an
  empty message and no key; `rng` is untouched.
- `States::from_pb` fails with `e`: `(Err e, rng)`.
- `States::send` fails with `e` and hands back `rng₁`: `(Err e, rng₁)`.
- `States::send` succeeds with `ss` and `rng₁`: `result.2` is `rng₁` and `result.1` satisfies
  `SendAfterStatesPost st ss` (see there).

Besides the errors of `States::from_pb` and `States::send`, the only errors are `StateDecode`,
`ChainNotAvailable`, `SendKeyEpochDecreased` and `EpochOutOfRange`.

**Source**: spqr/src/lib.rs (lines 271:0-331:1) -/
@[step]
theorem send_spec {R : Type} (rngInst : rand_1.rng.Rng R)
    (cryptoInst : rand_core_1.CryptoRng R) (state : alloc.vec.Vec U8) (rng : R)
    (h_ready : SendAssumptions rngInst cryptoInst state rng) :
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
            | .Ok ss => result.2 = rng₁ ∧ SendAfterStatesPost st ss result.1 ⦄ := by
  -- `Version::V0 as i32` (translated as the cast of `0 + 0`) is `0`.
  have h_v0 : (0#i32 + 0#i32 : Result I32) = ok 0#i32 ∧ IScalar.cast .I32 0#i32 = 0#i32 := by
    obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists
      (IScalar.add_spec (x := 0#i32) (y := 0#i32) (by scalar_tac) (by scalar_tac))
    exact ⟨by rw [hz, show z = 0#i32 by scalar_tac], rfl⟩
  -- Unfold `send` and resolve the `?` plumbing, the asserts and the constants everywhere.
  unfold send
  simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from, core.option.Option.as_ref, h_v0, bind_ok, lift, massert,
    alloc.vec.Vec.is_empty, alloc.vec.Vec.index_slice_index, core.convert.IntoFrom.into,
    U8.Insts.CoreConvertFromVersion.from]
  -- Early exits: a disabled ratchet, or an error of `decode_state`, `from_pb` or `States::send`.
  -- (For speed, here and below, `simp only` first drops the rest of the program, and `simp` skips
  -- `IsEmpty.*`, whose failing instance searches on `Error`, `R`, `States`, ... dominate its cost.)
  obtain ⟨d, hd, -⟩ := WP.spec_imp_exists (decode_state_spec state)
  rcases d with ⟨vno, cho, _ | ⟨⟨pb⟩⟩⟩ | e
  · simp only [hd, bind_ok]; simp [-IsEmpty.forall_iff, -IsEmpty.exists_iff]
  on_goal 2 => simp only [hd, bind_ok]; simp [-IsEmpty.forall_iff, -IsEmpty.exists_iff]
  obtain ⟨h_fp, h_ready⟩ := h_ready _ hd pb rfl
  obtain ⟨s | e, hr1, -⟩ := WP.spec_imp_exists h_fp
  on_goal 2 => simp only [hd, hr1, bind_ok]; simp [hr1, -IsEmpty.forall_iff, -IsEmpty.exists_iff]
  obtain ⟨h_st, h_ready⟩ := h_ready s hr1
  obtain ⟨⟨ss | e, rng₁⟩, hr2, -⟩ := WP.spec_imp_exists h_st
  on_goal 2 => simp only [hd, hr1, hr2, bind_ok, uncurry_apply_pair]; simp [hr1, hr2,
    -IsEmpty.forall_iff, -IsEmpty.exists_iff]
  -- `States::send` succeeds: the result is fixed by `SendAfterStatesPost`.
  obtain ⟨h_nc, h_cs⟩ := h_ready ss rng₁ hr2
  refine WP.spec_mono
    (P₀ := fun r => r.2 = rng₁ ∧ SendAfterStatesPost ⟨vno, cho, some (.V1 pb)⟩ ss r.1) ?_
    fun r h => by simp [hd, hr1, hr2, h, -IsEmpty.forall_iff, -IsEmpty.exists_iff]
  simp only [hd, hr1, hr2, bind_ok, uncurry_apply_pair]
  -- The message serialises to `messageBytes`: nonempty, with the version byte `1` first.
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
  · -- A chain `c` is selected. It is a well-formed deque (a decoded chain has `head = 0` and
    -- `length = buf.length`, a fresh one holds one epoch), and so is `c₁`, the chain with the
    -- epoch secret, if any, mixed in by `add_epoch`.
    obtain ⟨c, hcs⟩ := hsrc
    obtain ⟨h_e1, h_add, h_sk⟩ := h_cs c hcs
    have hwf : c.links.head.val + c.links.length.val ≤ c.links.buf.val.length := by
      rcases hcs with ⟨cpb, -, hc⟩ | ⟨-, vn, -, -, hc⟩
      · clear * - hc; grind [fromPb]
      unfold chainFromVersionNegotiation at hc
      (split at hc <;> try split at hc) <;> try simp at hc
      clear * - hc; grind [(WP.spec_ok _).mp (hc ▸ chain.Chain.new_spec _ _ _)]
    obtain ⟨c₁, hmix, hwf₁⟩ : ∃ c₁, ss.key.elim (ok c) c.add_epoch = ok c₁ ∧
        c₁.links.head.val + c₁.links.length.val ≤ c₁.links.buf.val.length := by
      rcases hk : ss.key with _ | k
      · exact ⟨c, rfl, hwf⟩
      obtain ⟨c₁, hc₁, h⟩ := WP.spec_imp_exists
        ((h_add k hk).elim (chain.Chain.add_epoch_spec c k · (by omega) ·))
      exact ⟨c₁, hc₁, by clear * - h hwf; grind⟩
    -- `send_key` runs on `c₁` for the epoch `e = msg.epoch - 1`.
    obtain ⟨e, he, he'⟩ := WP.spec_imp_exists (U64.sub_spec (y := 1#u64) h_e1)
    have he1 : e.val + 1 = ss.msg.epoch.val := by rw [he'.1]; exact Nat.sub_add_cancel h_e1
    obtain ⟨h_df, h_tg, h_ip⟩ := h_sk c₁ hmix e he1
    obtain ⟨⟨r₄, c₂⟩, hsk, hpost⟩ := WP.spec_imp_exists
      (chain.Chain.send_key_spec c₁ e h_df hwf₁ fun h₁ h₂ h₃ => by
        split <;> [trivial; exact h_tg h₁ h₂ h₃ _ ‹_›])
    have h_ok : ∀ i mk, r₄ = .Ok (i, mk) →
        c₂.links.head.val + c₂.links.length.val ≤ c₂.links.buf.val.length ∧ mk.val ≠ [] := by
      clear * - hpost; grind [chain.sendKeyPost, chain.sendKeyDequePost, chain.sendKeySlotPost]
    -- Split on the source of `c`. After the source-specific steps both goals are the same, and
    -- `SendAfterStatesPost` reduces to the `.Ok c` branch of its last clause.
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
      simp only [hsel, SendAfterStatesPost, reduceCtorEq, false_implies,
        Option.some.injEq, Option.mem_def, forall_eq',
        false_and, true_and, exists_eq_left', or_false, false_or, Result.ok.injEq, ← Int.not_lt,
        not_true_eq_false, exists_false]
      refine WP.spec_bind (Pₘ := (c₁ = ·)) ?_ fun _ h => h ▸ ?_
      · rcases hk : ss.key with _ | k <;> simp only [hk, Option.elim, Result.ok.injEq] at hmix <;>
          simp [hmix]
      simp only [he, hsk, bind_ok, uncurry_apply_pair]
      rcases r₄ with ⟨⟨i, mk⟩⟩ | err
      · -- `send_key` succeeds: serialise the chain, the message and the state.
        obtain ⟨hwf₂, hmk⟩ := h_ok i mk rfl
        obtain ⟨vs, hvs, -⟩ := WP.spec_imp_exists (h_ip i mk c₂ hsk)
        obtain ⟨msg, hmsg, hbytes, hne, hidx⟩ := h_ser i
        obtain ⟨cp, hcp, rfl⟩ := WP.spec_imp_exists (chain.Chain.into_pb_spec c₂ hwf₂)
        simp only [hcp, hmsg, List.isEmpty_iff, hne, hidx, hvs, hmk, bind_ok, uncurry_apply_pair,
          not_false_eq_true, ↓reduceIte]
        refine WP.spec_bind (encode_state_pb_spec _) fun v hv => (WP.spec_ok _).mpr ?_
        exact ⟨rfl, _, _, _, _, hmix, he1, hsk, hpost, _, vs, rfl, rfl, hv, hbytes, rfl⟩
      · -- `send_key` fails: its error is the result.
        simp only [bind_ok, bind_tc_ok, WP.spec_ok, true_and]
        exact ⟨_, _, _, _, hmix, he1, hsk, hpost, rfl⟩
  · -- No chain is selected: `ChainNotAvailable`, an error of the selection, or the no-chain path.
    simp only [SendAfterStatesPost]
    rcases cho with _ | cpb
    · rcases vno with _ | vn
      · -- No version negotiation either: `Err ChainNotAvailable`.
        exact (WP.spec_ok _).mpr ⟨rfl, fun _ => rfl, (fun ⟨_, _, h, _⟩ => nomatch h),
          fun | _, .inl ⟨_, h, _⟩ | _, .inr ⟨_, _, h, _⟩ => nomatch h⟩
      by_cases h_mv : 0 < vn.min_version.val
      · -- `chain_from_version_negotiation` fails.
        obtain ⟨c | e, hr3, hcf⟩ := WP.spec_imp_exists (chain_from_version_negotiation_spec vn)
        · exact (hsrc ⟨c, .inr ⟨rfl, vn, rfl, h_mv, hcf⟩⟩).elim
        simp [hr3, hcf, h_mv, -IsEmpty.forall_iff, -IsEmpty.exists_iff]
      · -- `min_version <= 0`, so no chain: the message is serialised with ratchet index `0`.
        obtain ⟨h_key, h_ip⟩ := h_nc ⟨rfl, vn, rfl, by omega⟩
        obtain ⟨vs, hvs, -⟩ := WP.spec_imp_exists h_ip
        obtain ⟨msg, hmsg, hbytes, hne, hidx⟩ := h_ser 0#u32
        obtain ⟨v, hv, hdec⟩ :=
          WP.spec_imp_exists (encode_state_pb_spec ⟨some vn, none, some (.V1 vs)⟩)
        simp [h_key, h_mv, core.option.Option.is_none, hmsg, hne, hidx,
          hvs, hv, hbytes, hdec, -IsEmpty.forall_iff, -IsEmpty.exists_iff]
    · -- A stored chain that `Chain::from_pb` rejects.
      obtain ⟨c | e, hr3, hfp⟩ := WP.spec_imp_exists (chain.Chain.from_pb_spec cpb)
      · exact (hsrc ⟨c, .inl ⟨cpb, rfl, hfp.symm⟩⟩).elim
      simp only [hr3, bind_ok, bind_tc_ok]
      simp [← hfp, -IsEmpty.forall_iff, -IsEmpty.exists_iff]

end spqr
