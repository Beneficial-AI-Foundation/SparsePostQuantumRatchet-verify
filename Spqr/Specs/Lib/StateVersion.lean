/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Lib.CurrentVersion
/-!
# Spec theorem for `spqr::state_version`

Extracts the protocol version implied by a `PqRatchetState`'s `inner` field:
`None` → `Version.V0` (PQ ratchet disabled), `Some _` → `Version.V1` (enabled).

The function is total — it always returns `ok` — and its result coincides with
the pure helper `innerVersion` defined in `Spqr.Specs.Lib.CurrentVersion`.

**Source**: spqr/src/lib.rs (lines 457:0-462:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/-- **Spec theorem for `spqr.state_version`**:

• Takes a `PqRatchetState` by (erased) reference.
• Pattern-matches on `state.inner`:
    - `none`   → returns `ok Version.V0`
    - `some _` → returns `ok Version.V1`
• The function always succeeds (no panic, no error path).
• The returned version equals `innerVersion state`.

**Source**: spqr/src/lib.rs (lines 457:0-462:1)
-/
@[step]
theorem state_version_spec (state : proto.pq_ratchet.PqRatchetState) :
    state_version state ⦃ (result : proto.pq_ratchet.Version) =>
      result = innerVersion state ⦄ := by
  unfold state_version innerVersion
  split <;> simp_all

end spqr
