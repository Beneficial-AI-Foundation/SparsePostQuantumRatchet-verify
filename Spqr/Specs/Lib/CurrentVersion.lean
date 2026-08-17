/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Lib.DecodeState
import Spqr.Specs.Lib.CurrentVersion.CallOnce
import Spqr.Specs.Proto.PqRatchet.Version.TryFrom
/-! # Spec theorem for `spqr::current_version`

Deserializes a `SerializedState` via `decode_state`, then reads `inner` (`None` → V0,
`Some` → V1) and `version_negotiation` (`None` → `NegotiationComplete`,
`Some vn` → `try_from(vn.min_version)` yielding `StillNegotiating` or `Err StateDecode`).
No panics; all errors surface as `Error::StateDecode`.

**Source**: spqr/src/lib.rs -/

open Aeneas Aeneas.Std Result

namespace spqr

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
          proto.pq_ratchet.PqRatchetState.Insts.ProstMessageMessage.encode_to_vec
            st = ok state ∧
          let v := match st.inner with
            | none => proto.pq_ratchet.Version.V0
            | some _ => proto.pq_ratchet.Version.V1
          match st.version_negotiation with
          | none => result = .Ok (CurrentVersion.NegotiationComplete v)
          | some vn =>
              (vn.min_version = 0#i32 →
                result = .Ok (CurrentVersion.StillNegotiating v proto.pq_ratchet.Version.V0)) ∧
              (vn.min_version = 1#i32 →
                result = .Ok (CurrentVersion.StillNegotiating v proto.pq_ratchet.Version.V1)) ∧
              (vn.min_version ≠ 0#i32 ∧
                vn.min_version ≠ 1#i32 →
                result = core.result.Result.Err Error.StateDecode))) ⦄ := by
  unfold current_version
  step*
  · match hr : r with
    | core.result.Result.Err e => simp_all
    | core.result.Result.Ok st =>
      simp only at cf_post
      rename_i h_eq
      have : st = val := by grind
      subst this
      · split
        · step*
          constructor
          · grind
          · intro hne
            right
            have henc := r_post2 hne
            simp only at henc
            exact ⟨st, henc, by simp_all⟩
          · rename_i r1_post
            split at r1_post
            · simp_all only [core.result.Result.Ok.injEq, ne_eq, core.result.Result.map_err_Ok,
              bind_tc_ok, IScalar.neq_to_neq_val, IScalar.ofInt_val_eq]
              step*
              exact And.intro (by intro hemp; grind)
                (by intro hne; right; exact ⟨st, r_post2 hne,
                by simp_all only [IsEmpty.forall_iff,
                  not_false_eq_true, forall_const, core.ops.control_flow.ControlFlow.Continue.injEq,
                  implies_true, core.result.Result.Ok.injEq, CurrentVersion.StillNegotiating.injEq,
                  reduceCtorEq, and_false, imp_false, IScalar.neq_to_neq_val, IScalar.ofInt_val_eq,
                  Decidable.not_not, true_and]; constructor <;> (simp [IScalar.val])⟩)
            · simp_all only [core.result.Result.Ok.injEq, ne_eq, core.result.Result.map_err_Ok,
              bind_tc_ok, IScalar.neq_to_neq_val, IScalar.ofInt_val_eq]
              step*
              exact And.intro (by intro hemp; grind)
                (by intro hne; right; exact ⟨st, r_post2 hne,
                by simp_all only [IsEmpty.forall_iff,
                  not_false_eq_true, forall_const, core.ops.control_flow.ControlFlow.Continue.injEq,
                  core.result.Result.Ok.injEq, CurrentVersion.StillNegotiating.injEq, reduceCtorEq,
                  and_false, imp_false, IScalar.neq_to_neq_val, IScalar.ofInt_val_eq, implies_true,
                  Decidable.not_not, true_and]; constructor <;> (simp [IScalar.val])⟩)
            · simp_all only [core.result.Result.Ok.injEq, ne_eq, imp_false, IScalar.neq_to_neq_val,
              core.result.Result.map_err_Err, bind_assoc, bind_tc_ok, IScalar.ofInt_val_eq]
              constructor
              · grind
              · intro hne
                left
                simp_all
        · step*
          · simp_all only [core.result.Result.Ok.injEq, ne_eq,
            CurrentVersion.NegotiationComplete.injEq, reduceCtorEq, imp_false,
            IScalar.neq_to_neq_val, IScalar.ofInt_val_eq, Decidable.not_not, false_or]
            constructor
            · grind
            · intro hne
              exact ⟨st, r_post2 hne, by simp_all⟩
          · simp_all only [core.result.Result.Ok.injEq, ne_eq, IScalar.neq_to_neq_val,
            IScalar.ofInt_val_eq]
            rename_i r1_post
            split at r1_post
            · simp_all only [core.result.Result.map_err_Ok, bind_tc_ok]
              step*
              exact And.intro (by intro hemp; grind)
                (by intro hne; right; exact ⟨st, r_post2 hne,
                by simp_all only [IsEmpty.forall_iff,
                  not_false_eq_true, forall_const, core.ops.control_flow.ControlFlow.Continue.injEq,
                  implies_true, core.result.Result.Ok.injEq, CurrentVersion.StillNegotiating.injEq,
                  reduceCtorEq, and_false, imp_false, IScalar.neq_to_neq_val, IScalar.ofInt_val_eq,
                  Decidable.not_not, true_and]; constructor <;> (simp [IScalar.val])⟩)
            · simp_all only [core.result.Result.map_err_Ok, bind_tc_ok]
              step*
              exact And.intro (by intro hemp; grind)
                (by intro hne; right; exact ⟨st, r_post2 hne,
                by simp_all only [IsEmpty.forall_iff,
                  not_false_eq_true, forall_const, core.ops.control_flow.ControlFlow.Continue.injEq,
                  core.result.Result.Ok.injEq, CurrentVersion.StillNegotiating.injEq, reduceCtorEq,
                  and_false, imp_false, IScalar.neq_to_neq_val, IScalar.ofInt_val_eq, implies_true,
                  Decidable.not_not, true_and]; constructor <;> (simp [IScalar.val])⟩)
            · simp_all only [imp_false, IScalar.neq_to_neq_val, core.result.Result.map_err_Err,
              bind_assoc, bind_tc_ok]
              constructor
              · grind
              · intro hne
                left
                simp_all
  · match hr : r with
    | core.result.Result.Ok st => simp_all
    | core.result.Result.Err e =>
      simp only at cf_post
      subst cf_post
      constructor
      · grind
      · intro hne
        left
        simp_all

end spqr
