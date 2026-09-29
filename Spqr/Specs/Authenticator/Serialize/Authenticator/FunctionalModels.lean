/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
import SrcTranslated.Types

/-!
# Functional models of `spqr::authenticator::serialize::Authenticator::{into_pb, from_pb}`

Pure, total Lean functions stating what the two Rust serializers compute, written against the
translated data types only, together with the two round-trip laws relating them. The spec
theorems in `IntoPb.lean` and `FromPb.lean` pin the extracted, monadic functions to these models.

**Source:** "spqr/src/authenticator/serialize.rs"
-/

namespace spqr.authenticator.serialize.Authenticator.FunctionalModels

/-- **Functional model of `spqr::authenticator::serialize::Authenticator::into_pb`**
• A pure, total, human-readable function on the translated data types.
-/
def intoPb (x : authenticator.Authenticator) : proto.pq_ratchet.Authenticator :=
  { root_key := x.root_key, mac_key := x.mac_key }

/-- **Functional model of `spqr::authenticator::serialize::Authenticator::from_pb`**
• A pure, total, human-readable function on the translated data types.
-/
def fromPb (pb : proto.pq_ratchet.Authenticator) : authenticator.Authenticator :=
  { root_key := pb.root_key, mac_key := pb.mac_key }

/-- **Round trip `fromPb ∘ intoPb` for `spqr::authenticator::serialize::Authenticator`** -/
@[simp]
theorem roundtrip_fromPb_intoPb (x : authenticator.Authenticator) :
    fromPb (intoPb x) = x := rfl

/-- **Round trip `intoPb ∘ fromPb` for `spqr::authenticator::serialize::Authenticator`** -/
@[simp]
theorem roundtrip_intoPb_fromPb (pb : proto.pq_ratchet.Authenticator) :
    intoPb (fromPb pb) = pb := rfl

end spqr.authenticator.serialize.Authenticator.FunctionalModels
