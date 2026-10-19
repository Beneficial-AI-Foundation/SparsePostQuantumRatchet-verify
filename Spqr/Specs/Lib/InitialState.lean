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

/-- **Spec theorem for `spqr.initial_state`** (V1 case):

• When `params.version = V1`, the function clones `params.auth_key`, converts
  `params.direction` and `params.min_version` to protobuf `i32` values, serialises
  `params.chain_params` via `ChainParams.into_pb`, initialises the inner state via
  `init_inner`, assembles a `PqRatchetState` protobuf message, and encodes it with
  `encode_state_pb`.
• Returns `Ok bytes` where `bytes` is a valid protobuf encoding that decodes back to
  the assembled `PqRatchetState`.
• Requires `auth_key.length + 32 ≤ Usize.max` (needed by `init_inner`) and
  `pk1_len = ok 64` (needed by the B2A branch for ML-KEM-768 header size).
• The function always succeeds (no panic) for valid V1 inputs.

The result satisfies the strong encoding postcondition:

  `∃ v, result = .Ok v ∧ ∃ st, decodesTo v st ∧
    st.chain = none ∧
    (∃ vs, st.inner = some (Inner.V1 vs)) ∧
    (∃ vn, st.version_negotiation = some vn ∧
      vn.auth_key.val = params.auth_key.val ∧
      vn.chain_params ≠ none)`

where `decodesTo` witnesses that the returned bytes can be decoded back to the ratchet state
that was assembled and encoded, and the additional conjuncts assert that:

1. `st.chain` is `none` (no chain state at initialisation),
2. `st.inner` wraps a `V1` inner state (established by `init_inner`),
3. `st.version_negotiation` is `some` and carries the cloned authentication key
   (byte-equal to `params.auth_key`) and a non-`none` chain_params.

**Source**: spqr/src/lib.rs (lines 219:0-242:1) -/
@[step]
theorem initial_state_spec_v1 (params : Params)
    (h_version : params.version = proto.pq_ratchet.Version.V1)
    (h_len : params.auth_key.length + 32 ≤ Usize.max)
    (h_pk1 : libcrux_ml_kem.mlkem768.incremental.pk1_len = ok 64#usize) :
    initial_state params ⦃ (result : core.result.Result (alloc.vec.Vec U8) Error) =>
      ∃ v : alloc.vec.Vec U8, result = .Ok v ∧
        ∃ st : proto.pq_ratchet.PqRatchetState, decodesTo v st ∧
          st.chain = none ∧
          (∃ vs, st.inner = some (proto.pq_ratchet.pq_ratchet_state.Inner.V1 vs)) ∧
          (∃ vn, st.version_negotiation = some vn ∧
            vn.auth_key.val = params.auth_key.val ∧
            vn.chain_params ≠ none) ⦄ := by
  unfold initial_state
  rw [h_version]
  step*
  exact ⟨v1, rfl, _,
    v1_post,
    rfl,
    ⟨vs, o_post ▸ rfl⟩,
    ⟨⟨v, i, i1, some cp⟩, rfl,
      by simp only [alloc.vec.Vec.val] at v_post ⊢; exact congrArg _ v_post.symm,
      by simp⟩⟩

end spqr
