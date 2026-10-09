/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Helper definitions for `spqr::msg_version`

Pure helper definitions used by the `msg_version` spec theorem.
-/

open Aeneas Aeneas.Std

namespace spqr

/-- The first byte of a message, if any. -/
def firstByte (msg : alloc.vec.Vec U8) : Option U8 :=
  msg.val.head?

/-- Interpret a first-byte value as a protocol version:
`0` → `V0`, `1` → `V1`, anything else → `none`. -/
def versionOfByte (b : U8) : Option proto.pq_ratchet.Version :=
  match b.val with
  | 0 => some proto.pq_ratchet.Version.V0
  | 1 => some proto.pq_ratchet.Version.V1
  | _ => none

/-- Expected result of `msg_version`: empty messages default to `V0`;
non-empty messages are classified by their first byte via `versionOfByte`. -/
def msgVersionExpected (msg : alloc.vec.Vec U8) : Option proto.pq_ratchet.Version :=
  match firstByte msg with
  | none   => some proto.pq_ratchet.Version.V0
  | some b => versionOfByte b

end spqr
