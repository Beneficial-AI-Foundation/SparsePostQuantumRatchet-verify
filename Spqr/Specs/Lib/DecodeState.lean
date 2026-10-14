/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Lib.DecodeState.CallOnce
public import Spqr.Specs.Lib.StatePb
/-! # Spec theorem for `spqr::decode_state`

Deserializes a `Vec<u8>` into a `PqRatchetState`. Empty input yields a default state (all `None`);
non-empty input delegates to `decode_state_pb` (prost's `PqRatchetState::decode`), mapping errors
to `Error::StateDecode`. The prost interface is axiomatized in `Spqr/Specs/Lib/StatePb.lean`.

**Source**: spqr/src/lib.rs (lines 472:0-482:1)
-/

@[expose] public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace spqr

/-- **Spec theorem for `spqr.decode_state`**:

- Empty `s`: returns `Ok` with default `PqRatchetState` (all fields `none`).
- Non-empty `s`: decodes via prost; `Ok pb` implies `pb` is what prost decodes from `s`
  (`decodesTo s pb`), `Err e` implies `e = Error.StateDecode`.
- Never panics; decode errors surface as `Result.Err`.

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
        | core.result.Result.Ok pb => decodesTo s pb
        | core.result.Result.Err e => e = Error.StateDecode) ⦄ := by
  unfold decode_state
  step*
  · simp_all
  · cases r with
    | Ok pb =>
      simp only [core.result.Result.map_err_Ok, spec_ok]
      simp_all [decodesTo]
    | Err e =>
      simp only [core.result.Result.map_err_Err]
      step*
      simp_all

/-- `decode_state` inverts `encode_state_pb` on non-empty encodings. -/
theorem decode_state_encode_state_pb (st : proto.pq_ratchet.PqRatchetState)
    (bytes : alloc.vec.Vec U8) (h : encode_state_pb st = ok bytes) (hne : bytes.val ≠ []) :
    decode_state bytes = ok (.Ok st) := by
  unfold decode_state
  simp only [alloc.vec.Vec.is_empty, alloc.vec.Vec.as_slice, bind_ok, List.isEmpty_iff, hne,
    ↓reduceIte]
  obtain ⟨bytes', h', hdec⟩ := WP.spec_imp_exists (encode_state_pb_spec st)
  obtain rfl := Result.ok_injective (h'.symm.trans h)
  rw [hdec _ (by simp)]
  simp only [bind_ok, core.result.Result.map_err_Ok]

end spqr
