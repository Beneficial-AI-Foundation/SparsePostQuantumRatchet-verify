/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::Version::MAX`

Alias for `Version::V1`, the highest supported protocol version.

**Source**: spqr/src/lib.rs (line 240)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.Version.MAX`**:

`Version.MAX = proto.pq_ratchet.Version.V1`. Complement of `Version.DISABLED` (`V0`). -/
@[simp]
theorem Version.MAX_spec :
    Version.MAX = proto.pq_ratchet.Version.V1 := by
  unfold Version.MAX; rfl

end spqr
