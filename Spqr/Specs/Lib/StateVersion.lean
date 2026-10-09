/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Lib.CurrentVersion
/-!
# Spec theorem for `spqr::state_version`

Maps `PqRatchetState.inner` to a protocol version (`None` → `V0`, `Some _` → `V1`).
Always succeeds; result equals `innerVersion`.

**Source**: spqr/src/lib.rs -/

open Aeneas Aeneas.Std Result

namespace spqr

/-- **Spec theorem for `spqr.state_version`**:
Always returns `ok (innerVersion state)`, matching `state.inner` to `V0`/`V1`. -/
@[step]
theorem state_version_spec (state : proto.pq_ratchet.PqRatchetState) :
    state_version state ⦃ (result : proto.pq_ratchet.Version) =>
      result = innerVersion state ⦄ := by
  unfold state_version innerVersion
  split <;> simp_all

end spqr
