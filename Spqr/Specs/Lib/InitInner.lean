/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import SrcTranslated.Funs
public import Spqr.Specs.V1.Chunked.SendEk.Serialize.KeysUnsampled.IntoPb
public import Spqr.Specs.V1.Unchunked.SendCt.Serialize.NoHeaderReceived.IntoPb
public import Spqr.Specs.Authenticator.Authenticator.New
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.New
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.IntoPb
/-!
# Spec theorem for `spqr::init_inner`

`init_inner` constructs the initial V1 protocol state wrapped in a protobuf `Inner` enum, or
returns `none` when the protocol version is `V0` (disabled).

The function dispatches on the `Version` / `Direction` pair:

| Version | Direction | Result                                        |
|---------|-----------|-----------------------------------------------|
| `V0`    | _any_     | `none` (protocol disabled, no inner state)     |
| `V1`    | `A2B`     | `some (Inner.V1 (States.init_a(auth_key).into_pb()))` |
| `V1`    | `B2A`     | `some (Inner.V1 (States.init_b(auth_key).into_pb()))` |

For `V0`, no key material is generated and no state machine is initialised — the caller receives
`none`, signalling that the post-quantum ratchet is inactive.

For `V1`, the function initialises the appropriate side of the ratchet state machine
(`init_a` for the A→B direction, `init_b` for the B→A direction), serialises the resulting
`States` value into its protobuf representation via `into_pb`, and wraps it in
`Inner.V1`.

**Source**: spqr/src/lib.rs (lines 198:0-210:1)
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.init_inner` (V0 case)**:

• When `v = Version.V0`, the function ignores `d` and `auth_key` and immediately returns
  `ok none`.
• No key material is generated; no state machine is initialised.

The result satisfies:

  `result = none`
-/
@[step]
theorem init_inner_spec_v0 (d : proto.pq_ratchet.Direction) (auth_key : Slice Std.U8) :
    init_inner proto.pq_ratchet.Version.V0 d auth_key
    ⦃ (result : Option proto.pq_ratchet.pq_ratchet_state.Inner) =>
      result = none ⦄ := by
  unfold init_inner
  simp

/--
**Spec theorem for `spqr.init_inner` (V1 / A2B case)**:

• When `v = Version.V1` and `d = Direction.A2B`, the function initialises party A's side of the
  ratchet via `States.init_a auth_key`, serialises the state via `States.into_pb`, and wraps the
  result in `some (Inner.V1 ·)`.
• The function succeeds whenever `auth_key.length + 32 ≤ Usize.max` (needed so that cloning
  the key and appending the 32-byte MAC key cannot overflow `usize`).
• The returned `V1State` contains a `KeysUnsampled` inner state, reflecting the initial
  send-encapsulation-key phase for party A.

The result satisfies:

  `match result with`
  `| some (Inner.V1 vs) => ∃ ku, vs.inner_state = some (InnerState.KeysUnsampled ku)`
  `| _ => False`
-/
theorem init_inner_spec_v1_a2b (auth_key : Slice Std.U8)
    (h_len : auth_key.length + 32 ≤ Usize.max) :
    init_inner proto.pq_ratchet.Version.V1 proto.pq_ratchet.Direction.A2B auth_key
    ⦃ (result : Option proto.pq_ratchet.pq_ratchet_state.Inner) =>
      match result with
      | some (proto.pq_ratchet.pq_ratchet_state.Inner.V1 vs) =>
        ∃ ku, vs.inner_state = some (proto.pq_ratchet.v1_state.InnerState.KeysUnsampled ku)
      | _ => False ⦄ := by
  unfold init_inner v1.chunked.states.States.init_a
    v1.chunked.states.serialize.States.into_pb
    v1.chunked.send_ek.KeysUnsampled.new
    v1.unchunked.send_ek.KeysUnsampled.new
  step*
  subst auth_key_post
  simpa [alloc.vec.Vec.length, alloc.vec.Vec.val] using h_len

/--
**Spec theorem for `spqr.init_inner` (V1 / B2A case)**:

• When `v = Version.V1` and `d = Direction.B2A`, the function initialises party B's side of the
  ratchet via `States.init_b auth_key`, serialises the state via `States.into_pb`, and wraps the
  result in `some (Inner.V1 ·)`.
• The function succeeds whenever `auth_key.length + 32 ≤ Usize.max`.  The ML-KEM-768
  header size comes from `libcrux_ml_kem.mlkem768.incremental.pk1_len`, which is modelled
  concretely in `SrcTranslated/FunsExternal.lean` as `ok 64`, so no extra hypothesis is needed.
• The returned `V1State` contains a `NoHeaderReceived` inner state, reflecting the initial
  send-ciphertext phase for party B (awaiting a header from A).

The result satisfies:

  `match result with`
  `| some (Inner.V1 vs) => ∃ nhr, vs.inner_state = some (InnerState.NoHeaderReceived nhr)`
  `| _ => False`
-/
@[step]
theorem init_inner_spec_v1_b2a (auth_key : Slice Std.U8)
    (h_len : auth_key.length + 32 ≤ Usize.max) :
    init_inner proto.pq_ratchet.Version.V1 proto.pq_ratchet.Direction.B2A auth_key
    ⦃ (result : Option proto.pq_ratchet.pq_ratchet_state.Inner) =>
      match result with
      | some (proto.pq_ratchet.pq_ratchet_state.Inner.V1 vs) =>
        ∃ nhr, vs.inner_state = some (proto.pq_ratchet.v1_state.InnerState.NoHeaderReceived nhr)
      | _ => False ⦄ := by
  unfold init_inner v1.chunked.states.States.init_b
    v1.chunked.states.serialize.States.into_pb
    v1.chunked.send_ct.NoHeaderReceived.new
    v1.unchunked.send_ct.NoHeaderReceived.new
    v1.chunked.send_ct.serialize.NoHeaderReceived.into_pb
  unfold incremental_mlkem768.HEADER_SIZE libcrux_ml_kem.mlkem768.incremental.pk1_len
  step*
  · simp only [UScalar.ofNatCore_val_eq, authenticator.Authenticator.MACSIZE, Nat.reduceAdd]
    scalar_tac
  · subst auth_key_post
    simpa [alloc.vec.Vec.length, alloc.vec.Vec.val] using h_len
  · simp_all only [Slice.length, authenticator.Authenticator.MACSIZE, UScalar.ofNatCore_val_eq,
    Nat.reduceAdd, Nat.reduceMod, ↓reduceIte, UScalarTy.Usize_numBits_eq, Nat.reduceDiv,
    List.reduceReplicate, alloc.vec.Vec.length, List.cons_append, List.nil_append,
    core.result.Result.expect]
    split <;> simp_all only [authenticator.Authenticator.MACSIZE_spec, Nat.reduceAdd, bind_ok]
    step*
    all_goals ((casesm* _ ∧ _); simp_all only [alloc.vec.Vec.length, List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd, getElem!_pos])
    · change (48 : ℕ) ≤ U32.max
      norm_num [U32.max, U32.numBits, UScalarTy.numBits]
    · intro j hj
      have hmem := List.getElem_mem (l := ([default, default, default, default, default,
          default, default, default, default, default, default, default, default, default,
          default, default] : List (sorted_vec.SortedSet spqr.encoding.polynomial.Pt)))
          (n := j) (h := by simpa using hj)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> rw [h] <;>
        simp only [default, alloc.vec.Vec.from_val, List.length_nil, mul_zero, zero_add, ge_iff_le]
        <;> scalar_tac

/--
**Spec theorem for `spqr.init_inner` (V1 case, any direction)**:

• When `v = Version.V1`, the function succeeds for either direction and returns
  `some (Inner.V1 vs)` for some `V1State` `vs`.
• Requires `auth_key.length + 32 ≤ Usize.max` (needed by both A2B and B2A branches).
• The postcondition asserts existence of the inner state **and** its direction-specific
  shape:
  - For `A2B`: the inner state is `KeysUnsampled`.
  - For `B2A`: the inner state is `NoHeaderReceived`.

The result satisfies:

  `∃ vs, result = some (Inner.V1 vs) ∧
    (d = .A2B → ∃ ku, vs.inner_state = some (InnerState.KeysUnsampled ku)) ∧
    (d = .B2A → ∃ nhr, vs.inner_state = some (InnerState.NoHeaderReceived nhr))`

This combined theorem is tagged `@[step]` so that `step*` can discharge `init_inner`
calls in downstream proofs (e.g. `initial_state_spec_v1`) without case-splitting on
direction.
-/
@[step]
theorem init_inner_spec_v1 (d : proto.pq_ratchet.Direction) (auth_key : Slice Std.U8)
    (h_len : auth_key.length + 32 ≤ Usize.max) :
    init_inner proto.pq_ratchet.Version.V1 d auth_key
    ⦃ (result : Option proto.pq_ratchet.pq_ratchet_state.Inner) =>
      ∃ vs, result = some (proto.pq_ratchet.pq_ratchet_state.Inner.V1 vs) ∧
        (d = proto.pq_ratchet.Direction.A2B →
          ∃ ku, vs.inner_state =
            some (proto.pq_ratchet.v1_state.InnerState.KeysUnsampled ku)) ∧
        (d = proto.pq_ratchet.Direction.B2A →
          ∃ nhr, vs.inner_state =
            some (proto.pq_ratchet.v1_state.InnerState.NoHeaderReceived nhr)) ⦄ := by
  cases d with
  | A2B =>
    exact Aeneas.Std.WP.spec_mono (init_inner_spec_v1_a2b auth_key h_len) fun r hr =>
      match r, hr with
      | some (proto.pq_ratchet.pq_ratchet_state.Inner.V1 vs), ⟨ku, hku⟩ =>
        ⟨vs, rfl, fun _ => ⟨ku, hku⟩, nofun⟩
  | B2A =>
    exact Aeneas.Std.WP.spec_mono (init_inner_spec_v1_b2a auth_key h_len) fun r hr =>
      match r, hr with
      | some (proto.pq_ratchet.pq_ratchet_state.Inner.V1 vs), ⟨nhr, hnhr⟩ =>
        ⟨vs, rfl, nofun, fun _ => ⟨nhr, hnhr⟩⟩

end spqr
