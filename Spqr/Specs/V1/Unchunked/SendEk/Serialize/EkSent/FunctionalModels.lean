/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
import SrcTranslated.Types
import Spqr.Specs.Authenticator.Serialize.Authenticator.FunctionalModels

/-!
# Functional models of `spqr::v1::unchunked::send_ek::serialize::EkSent::{into_pb, from_pb}`

Pure, total Lean functions stating what the two Rust serializers compute, written against the
translated data types only, together with the well-formedness predicate and the round-trip laws
relating them. The spec theorems in `IntoPb.lean` and `FromPb.lean` pin the extracted, monadic
functions to these models. The nested `Authenticator` is handled by calling its own functional
model.

The round-trip laws are three separate theorems:

• `roundtrip_fromPb_intoPb` (RT1): every well-formed in-memory state survives encoding followed by
  decoding unchanged.

• `wellFormed_of_fromPb` (RT2a): every protobuf state the decoder successfully decodes yields a
  well-formed in-memory state.

• `roundtrip_intoPb_fromPb` (RT2b): every protobuf state the decoder successfully decodes is the
  encoding of the associated in-memory state it decodes to.

RT1, RT2a and RT2b together imply that:

• `intoPb` and `fromPb` restrict to mutually inverse bijections between

  (i) the well-formed in-memory input states for `intoPb`, and

  (ii) the protobuf input states that `fromPb` successfully decodes.

• `WellFormed` characterises exactly the set of in-memory input states for `intoPb` that survive
  encoding followed by decoding unchanged.

**Source**: spqr/src/v1/unchunked/send_ek/serialize.rs
-/

open Aeneas.Std spqr.proto.pq_ratchet spqr.authenticator.serialize
namespace spqr.v1.unchunked.send_ek.serialize.EkSent.FunctionalModels

/-- **Functional model of `spqr::v1::unchunked::send_ek::serialize::EkSent::into_pb`**
• A pure, total, human-readable function on the translated data types.
• Delegates to `Authenticator.FunctionalModels.intoPb` and wraps the result in `some`.
-/
def intoPb (x : EkSent) : v1_state.unchunked.EkSent :=
  { epoch := x.epoch, auth := some (Authenticator.FunctionalModels.intoPb x.auth), dk := x.dk }

/-- **Functional model of `spqr::v1::unchunked::send_ek::serialize::EkSent::from_pb`**
• A pure, total, human-readable function on the translated data types.
• Delegates to `Authenticator.FunctionalModels.fromPb`; a `dk` that is not 2400 bytes long or an
  absent `auth` is `Error.StateDecode`.
-/
def fromPb (pb : v1_state.unchunked.EkSent) :
    core.result.Result EkSent Error :=
  match pb.auth, pb.dk.length with
  | some a, 2400 => .Ok { epoch := pb.epoch, auth := Authenticator.FunctionalModels.fromPb a,
                          dk := pb.dk }
  | _, _ => .Err Error.StateDecode

/-- **Well-formedness predicate for `spqr::v1::unchunked::send_ek::EkSent`**
• The in-memory states that survive a round trip: `dk` must be exactly 2400 bytes long.
• Transcribed from the `#[hax_lib::refine(dk.len() == 2400)]` annotation on the Rust struct.
-/
def WellFormed (x : EkSent) : Prop := x.dk.length = 2400

/-- **Round trip `fromPb ∘ intoPb` (RT1) for
`spqr::v1::unchunked::send_ek::serialize::EkSent`**
• Every well-formed in-memory state survives encoding followed by decoding unchanged. -/
@[simp]
theorem roundtrip_fromPb_intoPb (x : EkSent) (h : WellFormed x) :
    fromPb (intoPb x) = .Ok x := by
  unfold WellFormed at h
  unfold fromPb intoPb
  rw [h]
  rfl

/-- **Successfully decoded protobuf input states yield well-formed in-memory states (RT2a) for
`spqr::v1::unchunked::send_ek::serialize::EkSent`**
• Every in-memory state the decoder successfully produces satisfies `WellFormed`. -/
theorem wellFormed_of_fromPb (pb : v1_state.unchunked.EkSent) (x : EkSent)
    (h : fromPb pb = .Ok x) : WellFormed x := by
  unfold fromPb at h
  split at h
  · simp only [core.result.Result.Ok.injEq] at h
    subst h
    assumption
  · simp only [reduceCtorEq] at h

/-- **Round trip `intoPb ∘ fromPb` (RT2b) for
`spqr::v1::unchunked::send_ek::serialize::EkSent`**
• Every successfully decoded protobuf state is the encoding of the in-memory state it
  decodes to. -/
theorem roundtrip_intoPb_fromPb (pb : v1_state.unchunked.EkSent) (x : EkSent)
    (h : fromPb pb = .Ok x) : intoPb x = pb := by
  rcases pb with ⟨epoch, auth, dk⟩
  unfold fromPb at h
  split at h
  next a ha _ =>
    simp only [core.result.Result.Ok.injEq] at h
    subst h ha
    rw [intoPb, Authenticator.FunctionalModels.roundtrip_intoPb_fromPb a]
  next => simp only [reduceCtorEq] at h

end spqr.v1.unchunked.send_ek.serialize.EkSent.FunctionalModels
