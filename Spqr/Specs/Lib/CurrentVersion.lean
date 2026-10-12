/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Lib.DecodeState
public import Spqr.Specs.Lib.CurrentVersion.CallOnce
public import Spqr.Specs.Proto.PqRatchet.Version.TryFrom
/-! # Spec theorem for `spqr::current_version`

Deserializes a `SerializedState` via `decode_state`, then reads `inner` (`None` → V0,
`Some` → V1) and `version_negotiation` (`None` → `NegotiationComplete`,
`Some vn` → `try_from(vn.min_version)` yielding `StillNegotiating` or `Err StateDecode`).
No panics; all errors surface as `Error::StateDecode`.

**Source**: spqr/src/lib.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr

/-- Version implied by the presence of the `inner` field:
`none` → V0 (PQ ratchet disabled), `some _` → V1 (enabled). -/
def innerVersion (st : proto.pq_ratchet.PqRatchetState) : proto.pq_ratchet.Version :=
  match st.inner with
  | none => proto.pq_ratchet.Version.V0
  | some _ => proto.pq_ratchet.Version.V1

/-- `st` is a decoding of the serialized `state`: re-encoding `st` yields the
original bytes (canonical-form roundtrip property). -/
def decodesTo (state : alloc.vec.Vec U8) (st : proto.pq_ratchet.PqRatchetState) : Prop :=
  proto.pq_ratchet.PqRatchetState.Insts.ProstMessageMessage.encode_to_vec st = ok state

/-- Expected result of `current_version` for a successfully decoded state `st`:
no `version_negotiation` means negotiation is complete at `innerVersion st`;
otherwise `vn.min_version` is converted via `Version::try_from` — `0`/`1` give
`StillNegotiating` at V0/V1, anything else is a `StateDecode` error. -/
def negotiationOutcome (st : proto.pq_ratchet.PqRatchetState)
    (result : core.result.Result CurrentVersion Error) : Prop :=
  match st.version_negotiation with
  | none =>
      result = .Ok (CurrentVersion.NegotiationComplete (innerVersion st))
  | some vn =>
      (vn.min_version = 0#i32 →
        result = .Ok
          (CurrentVersion.StillNegotiating (innerVersion st) proto.pq_ratchet.Version.V0)) ∧
      (vn.min_version = 1#i32 →
        result = .Ok
          (CurrentVersion.StillNegotiating (innerVersion st) proto.pq_ratchet.Version.V1)) ∧
      (vn.min_version ≠ 0#i32 ∧ vn.min_version ≠ 1#i32 →
        result = core.result.Result.Err Error.StateDecode)

/-- **Spec theorem for `spqr.current_version`**:

Splits on `state.val = []` vs `≠ []`. Empty → `Ok (NegotiationComplete V0)`.
Non-empty → decode error gives `Err StateDecode`; decode success yields `∃ st`
with roundtrip, then `version_negotiation = none` → `NegotiationComplete v`,
`some vn` → `try_from vn.min_version` gives `StillNegotiating` or `Err StateDecode`. -/
@[step]
theorem current_version_spec (state : alloc.vec.Vec U8) :
    current_version state ⦃ (result : core.result.Result CurrentVersion Error) =>
      (state.val = [] →
        result = core.result.Result.Ok
          (CurrentVersion.NegotiationComplete proto.pq_ratchet.Version.V0)) ∧
      (state.val ≠ [] →
        (result = core.result.Result.Err Error.StateDecode) ∨
        (∃ st : proto.pq_ratchet.PqRatchetState,
          decodesTo state st ∧ negotiationOutcome st result)) ⦄ := by
  simp only [decodesTo, negotiationOutcome, innerVersion]
  unfold current_version
  step with decode_state_spec as ⟨r, h_emp, h_ne⟩
  cases r with
  | Err e =>
    step
    subst ‹cf = _›
    simp only
    step with core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual.spec
    simp_all
  | Ok st =>
    step*
    obtain rfl : val = st := by simp_all
    cases h1 : val.inner <;> cases h2 : val.version_negotiation <;> step*
    case none.none =>
      exact ⟨fun _ => trivial, fun hne => Or.inr ⟨val, h_ne hne, by simp [h1, h2]⟩⟩
    case some.none =>
      refine ⟨fun h => by cases h_emp h; simp at h1,
        fun hne => Or.inr ⟨val, h_ne hne, by simp [h1, h2]⟩⟩
    all_goals
      obtain hr1 := ‹r1 = _›
      split at hr1 <;> subst hr1
      case h_3 =>
        simp only [core.result.Result.map_err_Err]
        step
        step
        subst ‹_ = core.ops.control_flow.ControlFlow.Break _›
        simp only
        step with core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual.spec
        refine ⟨fun h => by cases h_emp h; simp at h2, fun _ => Or.inl (by simp_all)⟩
      all_goals
        simp only [core.result.Result.map_err_Ok]
        step*
        refine ⟨fun h => by cases h_emp h; simp at h2, fun hne => ?_⟩
        exact Or.inr ⟨val, h_ne hne, by
          simp_all [show (0#32#iscalar : I32).val = 0 from rfl,
            show (1#32#iscalar : I32).val = 1 from rfl]⟩

end spqr
