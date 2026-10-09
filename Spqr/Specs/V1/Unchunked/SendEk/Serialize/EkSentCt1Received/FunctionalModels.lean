/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
import SrcTranslated.Types
import Spqr.Specs.Authenticator.Serialize.Authenticator.FunctionalModels

/-!
# Functional models of
`spqr::v1::unchunked::send_ek::serialize::EkSentCt1Received::{into_pb, from_pb}`

Pure, total Lean functions stating what the two Rust serializers compute, written against the
translated data types only, together with the well-formedness predicate and the round-trip laws
relating them. The spec theorems in `IntoPb.lean` and `FromPb.lean` pin the extracted, monadic
functions to these models. The nested components are handled by calling their own functional
models: `auth` via `Authenticator.FunctionalModels`.

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
namespace spqr.v1.unchunked.send_ek.serialize.EkSentCt1Received.FunctionalModels

/-- **Functional model of `spqr::v1::unchunked::send_ek::serialize::EkSentCt1Received::into_pb`**
• A pure, total, human-readable function on the translated data types.
• Delegates to `Authenticator.FunctionalModels.intoPb` and wraps the result in `some`.
-/
def intoPb (x : EkSentCt1Received) : v1_state.unchunked.EkSentCt1Received :=
  { epoch := x.epoch, auth := some (Authenticator.FunctionalModels.intoPb x.auth), dk := x.dk,
    ct1 := x.ct1 }

/-- **Functional model of `spqr::v1::unchunked::send_ek::serialize::EkSentCt1Received::from_pb`**
• A pure, total, human-readable function on the translated data types.
• Delegates to `Authenticator.FunctionalModels.fromPb`; a `dk` that is not 2400 bytes long, a
  `ct1` that is not 960 bytes long or an absent `auth` is `Error.StateDecode`.
-/
def fromPb (pb : v1_state.unchunked.EkSentCt1Received) :
    core.result.Result EkSentCt1Received Error :=
  match pb.auth, pb.dk.length, pb.ct1.length with
  | some a, 2400, 960 => .Ok { epoch := pb.epoch, auth := Authenticator.FunctionalModels.fromPb a,
                               dk := pb.dk, ct1 := pb.ct1 }
  | _, _, _ => .Err Error.StateDecode

/-- **Well-formedness predicate for `spqr::v1::unchunked::send_ek::EkSentCt1Received`**
• The in-memory states that survive a round trip: `dk` must be exactly 2400 bytes long and
  `ct1` must be exactly 960 bytes long.
• Transcribed from the `#[hax_lib::refine(dk.len() == 2400)]` and
  `#[hax_lib::refine(ct1.len() == 960)]` annotations on the Rust struct.
-/
def WellFormed (x : EkSentCt1Received) : Prop := x.dk.length = 2400 ∧ x.ct1.length = 960

/-- **Round trip `fromPb ∘ intoPb` (RT1) for
`spqr::v1::unchunked::send_ek::serialize::EkSentCt1Received`**
• Every well-formed in-memory state survives encoding followed by decoding unchanged. -/
@[simp]
theorem roundtrip_fromPb_intoPb (x : EkSentCt1Received) (h : WellFormed x) :
    fromPb (intoPb x) = .Ok x := by
  unfold WellFormed at h
  obtain ⟨h1, h2⟩ := h
  unfold fromPb intoPb
  rw [h1, h2]
  rfl

/-- **Successfully decoded protobuf input states yield well-formed in-memory states (RT2a) for
`spqr::v1::unchunked::send_ek::serialize::EkSentCt1Received`**
• Every in-memory state the decoder successfully produces satisfies `WellFormed`. -/
theorem wellFormed_of_fromPb (pb : v1_state.unchunked.EkSentCt1Received) (x : EkSentCt1Received)
    (h : fromPb pb = .Ok x) : WellFormed x := by
  unfold fromPb at h
  split at h
  · simp only [core.result.Result.Ok.injEq] at h
    subst h
    exact ⟨‹_›, ‹_›⟩
  · simp only [reduceCtorEq] at h

/-- **Round trip `intoPb ∘ fromPb` (RT2b) for
`spqr::v1::unchunked::send_ek::serialize::EkSentCt1Received`**
• Every successfully decoded protobuf state is the encoding of the in-memory state it
  decodes to. -/
theorem roundtrip_intoPb_fromPb (pb : v1_state.unchunked.EkSentCt1Received) (x : EkSentCt1Received)
    (h : fromPb pb = .Ok x) : intoPb x = pb := by
  rcases pb with ⟨epoch, auth, dk, ct1⟩
  unfold fromPb at h
  split at h
  next a ha _ _ =>
    simp only [core.result.Result.Ok.injEq] at h
    subst h ha
    rw [intoPb, Authenticator.FunctionalModels.roundtrip_intoPb_fromPb a]
  next => simp only [reduceCtorEq] at h

end spqr.v1.unchunked.send_ek.serialize.EkSentCt1Received.FunctionalModels
