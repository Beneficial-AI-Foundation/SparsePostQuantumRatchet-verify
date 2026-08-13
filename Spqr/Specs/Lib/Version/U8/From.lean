/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-! # Spec theorem for `spqr::{impl From<Version> for u8}::from`

Converts `Version` to `u8` (`V0 → 0`, `V1 → 1`). Total, injective, and round-trips with
`TryFrom<u8>`: `TryFrom::try_from(From::from(v)) = Ok(v)`.

**Source**: spqr/src/lib.rs -/

open Aeneas Aeneas.Std Result

namespace spqr.U8.Insts.CoreConvertFromVersion

/-- **Spec theorem for `spqr.U8.Insts.CoreConvertFromVersion.from`**:

Maps `V0 → 0#u8`, `V1 → 1#u8`. Always succeeds; injective.
Postcondition: `(v = .V0 ↔ result = 0#u8) ∧ (v = .V1 ↔ result = 1#u8)`. -/
@[step]
theorem from_spec (v : proto.pq_ratchet.Version) :
    U8.Insts.CoreConvertFromVersion.from v ⦃ (result : U8) =>
      (v = .V0 ↔ result = 0#u8) ∧
      (v = .V1 ↔ result = 1#u8) ⦄ := by
  unfold U8.Insts.CoreConvertFromVersion.from
  match v with
  | .V0 => simp
  | .V1 => simp

end spqr.U8.Insts.CoreConvertFromVersion
