/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Lib.EmptyState
public import Spqr.Specs.Proto.PqRatchet.Direction.From
public import Spqr.Specs.Proto.PqRatchet.Version.From
public import Spqr.Specs.Chain.ChainParams.IntoPb
public import Spqr.Specs.Lib.InitInner
public import Spqr.Specs.Lib.StatePb
/-!
# Spec theorem for `spqr::initial_state`

`initial_state` constructs the serialised protocol state for a freshly initialised SPQR session.
Its behaviour depends on `params.version`:

  1. **V0 (disabled)**:  delegates to `empty_state`, which returns an empty byte vector, and wraps
     the result in `Ok`.  No key material is generated.
  2. **V1**:  clones the authentication key, converts the direction and minimum version to their
     protobuf `i32` representations, serialises the chain parameters, calls `init_inner` to
     construct the version-specific inner state, assembles a full `PqRatchetState` protobuf
     message, encodes it via `encode_state_pb`, and returns the resulting bytes wrapped in `Ok`.

The function always returns `Ok` (never `Err`) for valid inputs and never panics.

**Source**: spqr/src/lib.rs (lines 219:0-242:1)
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr

/-- **Spec theorem for `spqr.initial_state`** (V0 case):

• When `params.version = V0`, the function delegates to `empty_state` and returns
  `Ok result` where `result.val = []`.
• The function always succeeds (no panic) for V0 inputs.

The result satisfies the emptiness postcondition:

  `∃ v, result = .Ok v ∧ v.val = []`

i.e., the returned vector contains no bytes, representing the V0 (disabled) protocol state.

**Source**: spqr/src/lib.rs (lines 219:0-242:1) -/
@[step]
theorem initial_state_spec_v0 (params : Params)
    (h_version : params.version = proto.pq_ratchet.Version.V0) :
    initial_state params ⦃ (result : core.result.Result (alloc.vec.Vec U8) Error) =>
      ∃ v : alloc.vec.Vec U8, result = .Ok v ∧ v.val = [] ⦄ := by
  unfold initial_state
  rw [h_version]
  step*

/-- Predicate: the V1 inner state is direction-appropriate.

- **A→B** direction ⟹ inner state is `KeysUnsampled` (waiting to sample keys).
- **B→A** direction ⟹ inner state is `NoHeaderReceived` (waiting for the first header). -/
def V1InnerStateMatchesDirection
    (dir : proto.pq_ratchet.Direction)
    (vs : proto.pq_ratchet.V1State) : Prop :=
  (dir = .A2B →
    ∃ ku, vs.inner_state =
      some (proto.pq_ratchet.v1_state.InnerState.KeysUnsampled ku)) ∧
  (dir = .B2A →
    ∃ nhr, vs.inner_state =
      some (proto.pq_ratchet.v1_state.InnerState.NoHeaderReceived nhr))

/-- Predicate: version-negotiation metadata matches the input parameters.

Checks that:
1. The auth key is cloned byte-for-byte from `params.auth_key`.
2. The direction is encoded as protobuf `i32` (`A2B ↦ 0`, `B2A ↦ 1`).
3. The minimum version is encoded as protobuf `i32` (`V0 ↦ 0`, `V1 ↦ 1`).
4. Chain parameters are exactly the protobuf conversion of `params.chain_params`
   (via `chain.ChainParams.into_pb`). -/
def VersionNegotiationMatchesParams
    (vn : proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    (params : Params) : Prop :=
  vn.auth_key.val = params.auth_key.val ∧
  vn.direction = (match params.direction with
    | .A2B => 0#iscalar | .B2A => 1#iscalar) ∧
  vn.min_version = (match params.min_version with
    | .V0 => 0#iscalar | .V1 => 1#iscalar) ∧
  ∃ cp, vn.chain_params = some cp ∧
    chain.ChainParams.into_pb params.chain_params = ok cp

/-- Predicate: a `PqRatchetState` is a well-formed V1 initial state for the given `params`.

A well-formed V1 initial state has:
1. **No chain** — `chain = none` (fresh session, no messages exchanged yet).
2. **V1 inner state** — wraps a `V1State` whose sub-state is direction-appropriate
   (see `V1InnerStateMatchesDirection`).
3. **Version negotiation** — carries the auth key, direction, min version, and chain
   params faithfully transcribed from `params` (see `VersionNegotiationMatchesParams`). -/
def IsWellFormedV1InitialState
    (st : proto.pq_ratchet.PqRatchetState)
    (params : Params) : Prop :=
  st.chain = none ∧
  (∃ vs, st.inner = some (proto.pq_ratchet.pq_ratchet_state.Inner.V1 vs) ∧
    V1InnerStateMatchesDirection params.direction vs) ∧
  (∃ vn, st.version_negotiation = some vn ∧
    VersionNegotiationMatchesParams vn params)

/-- **Spec theorem for `spqr.initial_state`** (V1 case):

• When `params.version = V1`, the function always succeeds and returns `Ok bytes`
  where `bytes` is a valid protobuf encoding of a `PqRatchetState` that is a
  well-formed V1 initial state for the given `params`.
• Requires `auth_key.length + 32 ≤ Usize.max` and `pk1_len = ok 64`.

**Source**: spqr/src/lib.rs (lines 219:0-242:1) -/
@[step]
theorem initial_state_spec_v1 (params : Params)
    (h_version : params.version = proto.pq_ratchet.Version.V1)
    (h_len : params.auth_key.length + 32 ≤ Usize.max)
    (h_pk1 : libcrux_ml_kem.mlkem768.incremental.pk1_len = ok 64#usize) :
    initial_state params ⦃ (result : core.result.Result (alloc.vec.Vec U8) Error) =>
      ∃ v : alloc.vec.Vec U8, result = .Ok v ∧
        ∃ st : proto.pq_ratchet.PqRatchetState, decodesTo v st ∧
          IsWellFormedV1InitialState st params ⦄ := by
  unfold IsWellFormedV1InitialState VersionNegotiationMatchesParams V1InnerStateMatchesDirection
  unfold initial_state
  rw [h_version]
  step as ⟨v, v_post⟩
  step
  step
  -- `step` would discard the `into_pb … = ok cp` equation, which the chain-params conjunct of
  -- `VersionNegotiationMatchesParams` needs.  `into_pb` is total (two `if`s and a struct
  -- literal), so obtain the equation directly and rewrite with it.
  obtain ⟨cp, h_cp⟩ : ∃ cp, chain.ChainParams.into_pb params.chain_params = ok cp := by
    unfold chain.ChainParams.into_pb
    split <;> split <;> simp
  rw [h_cp]
  step*
  refine ⟨v1, rfl, _, v1_post, rfl,
    ⟨vs, o_post ▸ rfl, o_post1, o_post2⟩,
    ⟨⟨v, i, i1, some cp⟩, rfl, ?_, i_post ▸ rfl, i1_post ▸ rfl, ?_⟩⟩
  · simp only [alloc.vec.Vec.val] at v_post ⊢
    exact congrArg _ v_post.symm
  · rfl

end spqr
