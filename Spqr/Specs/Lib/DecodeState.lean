/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Lib.DecodeState.CallOnce
/-! # Spec theorem for `spqr::decode_state`

Deserializes a `Vec<u8>` into a `PqRatchetState`. Empty input yields a default state (all `None`);
non-empty input delegates to `PqRatchetState::decode`, mapping errors to `Error::StateDecode`.
Roundtrip correctness is axiomatized in `Axioms.lean`.

**Source**: spqr/src/lib.rs (lines 472:0-482:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/-- **Spec theorem for `spqr.decode_state`**:

- Empty `s`: returns `Ok` with default `PqRatchetState` (all fields `none`).
- Non-empty `s`: decodes via prost; `Ok pb` implies `encode_to_vec pb = ok s`,
  `Err e` implies `e = Error.StateDecode`.
- Never panics; decode errors surface as `Result.Err`.
- Non-empty branch relies on `protobuf_decode_encode_roundtrip` axiom.

**Source**: spqr/src/lib.rs (lines 472:0-482:1)
-/
@[step]
theorem decode_state_spec (s : alloc.vec.Vec U8) :
    decode_state s ⦃ (result : core.result.Result proto.pq_ratchet.PqRatchetState Error) =>
      (s.val = [] →
        result = core.result.Result.Ok
        { version_negotiation := none, chain := none, inner := none }) ∧
      (s.val ≠ [] →
        match result with
        | core.result.Result.Ok pb =>
            proto.pq_ratchet.PqRatchetState.Insts.ProstMessageMessage.encode_to_vec pb = ok s
        | core.result.Result.Err e => e = Error.StateDecode) ⦄ := by
  unfold decode_state
  step*
  · simp_all
  · simp_all
    -- Cannot complete this proof because it requires unfolding
    -- `proto.pq_ratchet.PqRatchetState.Insts.ProstMessageMessage`, which is the
    -- `prost::message::Message` trait impl for `PqRatchetState`. That definition is
    -- auto-generated protobuf serialization code replaced with `sorry` during translation
    -- (see aeneas-config.yml and https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/102).
    -- Until that trait impl is properly specified, the decode-encode roundtrip property
    -- in the non-empty branch cannot be discharged.
    -- TODO: #102
    sorry

end spqr
