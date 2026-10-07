/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
import SrcTranslated.Types
import Spqr.Specs.Authenticator.Serialize.Authenticator.FunctionalModels

/-!
# Functional models of
`spqr::v1::unchunked::send_ct::serialize::NoHeaderReceived::{into_pb, from_pb}`

Pure, total Lean functions stating what the two Rust serializers compute, written against the
translated data types only, together with the round-trip laws relating them. The spec theorems
in `IntoPb.lean` and `FromPb.lean` pin the extracted, monadic functions to these models. The
nested `Authenticator` is handled by calling its own functional model.

**Source**: spqr/src/v1/unchunked/send_ct/serialize.rs
-/

open Aeneas.Std spqr.proto.pq_ratchet spqr.authenticator.serialize
namespace spqr.v1.unchunked.send_ct.serialize.NoHeaderReceived.FunctionalModels

/-- **Functional model of `spqr::v1::unchunked::send_ct::serialize::NoHeaderReceived::into_pb`**
• A pure, total, human-readable function on the translated data types.
• Delegates to `Authenticator.FunctionalModels.intoPb` and wraps the result in `some`.
-/
def intoPb (x : NoHeaderReceived) : v1_state.unchunked.NoHeaderReceived :=
  { epoch := x.epoch, auth := some (Authenticator.FunctionalModels.intoPb x.auth) }

/-- **Functional model of `spqr::v1::unchunked::send_ct::serialize::NoHeaderReceived::from_pb`**
• A pure, total, human-readable function on the translated data types.
• Delegates to `Authenticator.FunctionalModels.fromPb`; absent input is `Error.StateDecode`.
-/
def fromPb (pb : v1_state.unchunked.NoHeaderReceived) :
    core.result.Result NoHeaderReceived Error :=
  match pb.auth with
  | none   => .Err Error.StateDecode
  | some a => .Ok { epoch := pb.epoch, auth := Authenticator.FunctionalModels.fromPb a }

/-- **Round trip `fromPb ∘ intoPb` for
`spqr::v1::unchunked::send_ct::serialize::NoHeaderReceived`** -/
@[simp]
theorem roundtrip_fromPb_intoPb (x : NoHeaderReceived) : fromPb (intoPb x) = .Ok x := rfl

/-- **Round trip `intoPb ∘ fromPb` for
`spqr::v1::unchunked::send_ct::serialize::NoHeaderReceived`** -/
theorem roundtrip_intoPb_fromPb (pb : v1_state.unchunked.NoHeaderReceived) (x : NoHeaderReceived)
    (h : fromPb pb = .Ok x) : intoPb x = pb := by
  rcases pb with ⟨epoch, _ | a⟩
  · simp [fromPb] at h
  · simp only [fromPb, core.result.Result.Ok.injEq] at h
    rw [intoPb, ← h, Authenticator.FunctionalModels.roundtrip_intoPb_fromPb a]

end spqr.v1.unchunked.send_ct.serialize.NoHeaderReceived.FunctionalModels
