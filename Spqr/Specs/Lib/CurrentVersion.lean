/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Lib.DecodeState
import Spqr.Specs.Lib.CurrentVersion.closure.CallOnce
import Spqr.Specs.Proto.PqRatchet.Version.TryFrom
/-!
# Spec theorem for `spqr::current_version`

`current_version` deserializes a `SerializedState` (a `Vec<u8>`) via `decode_state`, then inspects
the resulting `PqRatchetState` to determine the current protocol version and negotiation status.

The logic proceeds as follows:

  1. Call `decode_state(state)` to obtain a `PqRatchetState` (or propagate an error via `?`).

  2. Determine the **version**:
     - If `inner` is `None` → `Version::V0`
     - If `inner` is `Some(_)` → `Version::V1`

  3. Inspect the **version negotiation** field:
     - If `version_negotiation` is `None` → return `CurrentVersion::NegotiationComplete(version)`
     - If `version_negotiation` is `Some(vn)` → attempt to convert `vn.min_version` (an `i32`)
       to a `Version` via `Version::try_from`, mapping any `UnknownEnumValue` error to
       `Error::StateDecode`.  On success, return
       `CurrentVersion::StillNegotiating(version, min_version)`.

The function always succeeds at the monadic level (no panic); protobuf decode errors and unknown
enum values are surfaced as `Error::StateDecode` inside the inner `Result`.

**Source**: spqr/src/lib.rs (lines 249:0-262:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.current_version`** (functional-correctness version):

• Takes a serialized state `state` (a `Vec<u8>`).
• Delegates to `decode_state` to obtain a `PqRatchetState`, propagating any decode error.
• Determines `version` from `inner`: `none → V0`, `some _ → V1`.
• Inspects `version_negotiation`:
  - `none` → returns `Ok (NegotiationComplete version)`
  - `some vn` → converts `vn.min_version` via `try_from`; on success returns
    `Ok (StillNegotiating version min_version)`, on failure returns `Err StateDecode`.

The postcondition uses a disjunction on `state.val = []` vs `state.val ≠ []`.
For the non-empty case, a further disjunction separates the decode-error case
(`result = Err StateDecode`) from the decode-success case, which introduces an
existential `∃ st` with the roundtrip property from `decode_state_spec`.
A nested `match` on `version_negotiation` and a disjunction on `vn.min_version`
complete the case split.

`decode_state` has two branches determined entirely by `state.val`:
  - `state.val = []`  → always returns `Ok { version_negotiation := none, chain := none, inner := none }`
  - `state.val ≠ []`  → delegates to the opaque protobuf `PqRatchetState.decode`, which may
                         succeed with some `st` or fail (mapped to `Error.StateDecode`).

**Case 1 — Empty state** (`state.val = []`):
  The default `PqRatchetState` has `inner = none`, `version_negotiation = none`.
  ⟹ `result = Ok (NegotiationComplete V0)`

**Case 2 — Non-empty state, protobuf decode error**:
  `state.val ≠ []` and the opaque protobuf decode of `state` fails.
  ⟹ `result = Err StateDecode`

**Case 3 — Non-empty state, decode success, `version_negotiation = none`**:
  `state.val ≠ []` and the protobuf decode yields `st` with `st.version_negotiation = none`.
  ⟹ `result = Ok (NegotiationComplete v)` where `v` is determined by `st.inner`

**Case 4 — Non-empty state, decode success, `version_negotiation = some vn`,
           `vn.min_version = 0`**:
  ⟹ `result = Ok (StillNegotiating v V0)` where `v` is determined by `st.inner`

**Case 5 — Non-empty state, decode success, `version_negotiation = some vn`,
           `vn.min_version = 1`**:
  ⟹ `result = Ok (StillNegotiating v V1)` where `v` is determined by `st.inner`

**Case 6 — Non-empty state, decode success, `version_negotiation = some vn`,
           `vn.min_version ∉ {0, 1}`**:
  ⟹ `result = Err StateDecode`

**Source**: spqr/src/lib.rs (lines 249:0-262:1)
-/
@[step]
theorem current_version_spec (state : alloc.vec.Vec U8) :
    current_version state ⦃ (result : core.result.Result CurrentVersion Error) =>
      -- Case 1: empty state, default PqRatchetState (all fields none), NegotiationComplete V0
      (state.val = [] →
        result = core.result.Result.Ok
          (CurrentVersion.NegotiationComplete proto.pq_ratchet.Version.V0)) ∧
      -- Cases 2–6: non-empty state, determined by decode_state result
      (state.val ≠ [] →
        -- Case 2: protobuf decode fails, StateDecode
        (result = core.result.Result.Err Error.StateDecode) ∨
        -- Cases 3–6: decode succeeds with some st (whose re-encoding yields state)
        (∃ st : proto.pq_ratchet.PqRatchetState,
          proto.pq_ratchet.PqRatchetState.Insts.ProstMessageMessage.encode_to_vec
            st = ok state ∧
          let v := match st.inner with
            | none => proto.pq_ratchet.Version.V0
            | some _ => proto.pq_ratchet.Version.V1
          match st.version_negotiation with
          | none =>
              -- Case 3: no version negotiation, NegotiationComplete
              result = .Ok (CurrentVersion.NegotiationComplete v)
          | some vn =>
              -- Case 4: min_version = 0
              (vn.min_version = 0#i32 →
                result = .Ok (CurrentVersion.StillNegotiating v proto.pq_ratchet.Version.V0)) ∧
              -- Case 5: min_version = 1
              (vn.min_version = 1#i32 →
                result = .Ok (CurrentVersion.StillNegotiating v proto.pq_ratchet.Version.V1)) ∧
              -- Case 6: unknown min_version
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
          · intro hemp
            rename_i r_post1
            grind
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
              · intro hemp; grind
              · intro hne; left; simp_all
        · step*
          · simp_all only [core.result.Result.Ok.injEq, ne_eq,
            CurrentVersion.NegotiationComplete.injEq, reduceCtorEq, imp_false,
            IScalar.neq_to_neq_val, IScalar.ofInt_val_eq, Decidable.not_not, false_or]
            constructor
            · intro hemp
              grind
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
              · intro hemp
                grind
              · intro hne
                left
                simp_all
  · match hr : r with
    | core.result.Result.Ok st => simp_all
    | core.result.Result.Err e =>
      simp only at cf_post
      subst cf_post
      constructor
      · intro hemp
        grind
      · intro hne
        left
        simp_all

end spqr
