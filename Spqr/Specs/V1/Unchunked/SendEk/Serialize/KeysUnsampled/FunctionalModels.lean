/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
import SrcTranslated.Types
import Spqr.Specs.Authenticator.Serialize.Authenticator.FunctionalModels

/-!
# Functional models of `spqr::v1::unchunked::send_ek::serialize::KeysUnsampled::{into_pb, from_pb}`

Pure, total Lean functions stating what the two Rust serializers compute, written against the
translated data types only, together with the round-trip laws relating them. The spec theorems
in `IntoPb.lean` and `FromPb.lean` pin the extracted, monadic functions to these models. The
nested `Authenticator` is handled by calling its own functional model.

**Source**: spqr/src/v1/unchunked/send_ek/serialize.rs
-/

open Aeneas.Std spqr.proto.pq_ratchet
open spqr.authenticator.serialize
namespace spqr.v1.unchunked.send_ek.serialize.KeysUnsampled.FunctionalModels

/-- **Functional model of `spqr::v1::unchunked::send_ek::serialize::KeysUnsampled::into_pb`**
• A pure, total, human-readable function on the translated data types.
• Serializes the nested authenticator with `Authenticator.intoPb` and wraps it in `some`.
-/
def intoPb (x : KeysUnsampled) : v1_state.unchunked.KeysUnsampled :=
  { epoch := x.epoch, auth := some (Authenticator.FunctionalModels.intoPb x.auth) }

/-- **Functional model of `spqr::v1::unchunked::send_ek::serialize::KeysUnsampled::from_pb`**
• A pure, total, human-readable function on the translated data types.
• Decodes the nested authenticator via `Authenticator.fromPb`; absent input is `Error.StateDecode`.
-/
def fromPb (pb : v1_state.unchunked.KeysUnsampled) :
    core.result.Result KeysUnsampled Error :=
  match pb.auth with
  | none   => .Err Error.StateDecode
  | some a => .Ok { epoch := pb.epoch, auth := Authenticator.FunctionalModels.fromPb a }

/-- **Round trip `fromPb ∘ intoPb` for
`spqr::v1::unchunked::send_ek::serialize::KeysUnsampled`** -/
@[simp]
theorem roundtrip_fromPb_intoPb (x : KeysUnsampled) : fromPb (intoPb x) = .Ok x := rfl

/-- **Round trip `intoPb ∘ fromPb` for
`spqr::v1::unchunked::send_ek::serialize::KeysUnsampled`** -/
theorem roundtrip_intoPb_fromPb (pb : v1_state.unchunked.KeysUnsampled) (x : KeysUnsampled)
    (h : fromPb pb = .Ok x) : intoPb x = pb := by
  rcases pb with ⟨epoch, _ | a⟩
  · simp [fromPb] at h
  · simp only [fromPb, core.result.Result.Ok.injEq] at h
    rw [intoPb, ← h, Authenticator.FunctionalModels.roundtrip_intoPb_fromPb a]

end spqr.v1.unchunked.send_ek.serialize.KeysUnsampled.FunctionalModels
