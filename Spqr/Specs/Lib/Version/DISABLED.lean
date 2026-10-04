/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-! # Spec theorem for `spqr::{spqr::proto::pq_ratchet::Version}::DISABLED`

`DISABLED` is an alias for `Version.V0`, indicating a disabled post-quantum ratchet.
The spec asserts `Version.DISABLED = .V0`.

**Source**: spqr/src/lib.rs -/

open Aeneas Aeneas.Std Result

namespace spqr.Version

/-- **Spec theorem for `spqr.Version.DISABLED`**:

`DISABLED` equals `Version.V0`. -/
@[simp]
theorem DISABLED_spec :
    DISABLED = proto.pq_ratchet.Version.V0 := by
  unfold DISABLED
  rfl

end spqr.Version
