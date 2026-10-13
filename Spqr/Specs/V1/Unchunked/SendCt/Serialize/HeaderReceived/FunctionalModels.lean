/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
module

public import SrcTranslated.Types
public import Spqr.Specs.Authenticator.Serialize.Authenticator.FunctionalModels

/-!
# Functional models of `spqr::v1::unchunked::send_ct::serialize::HeaderReceived::{into_pb, from_pb}`

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

**Source**: spqr/src/v1/unchunked/send_ct/serialize.rs
-/

@[expose] public section

open Aeneas.Std spqr.proto.pq_ratchet spqr.authenticator.serialize
namespace spqr.v1.unchunked.send_ct.serialize.HeaderReceived.FunctionalModels

/-- **Functional model of `spqr::v1::unchunked::send_ct::serialize::HeaderReceived::into_pb`**
• A pure, total, human-readable function on the translated data types.
• Delegates to `Authenticator.FunctionalModels.intoPb` and wraps the result in `some`.
-/
def intoPb (x : HeaderReceived) : v1_state.unchunked.HeaderReceived :=
  { epoch := x.epoch, auth := some (Authenticator.FunctionalModels.intoPb x.auth), hdr := x.hdr }

/-- **Functional model of `spqr::v1::unchunked::send_ct::serialize::HeaderReceived::from_pb`**
• A pure, total, human-readable function on the translated data types.
• Delegates to `Authenticator.FunctionalModels.fromPb`; a `hdr` that is not 64 bytes long or an
  absent `auth` is `Error.StateDecode`.
-/
def fromPb (pb : v1_state.unchunked.HeaderReceived) :
    core.result.Result HeaderReceived Error :=
  match pb.auth, pb.hdr.length with
  | some a, 64 => .Ok { epoch := pb.epoch, auth := Authenticator.FunctionalModels.fromPb a,
                        hdr := pb.hdr }
  | _, _ => .Err Error.StateDecode

/-- **Well-formedness predicate for `spqr::v1::unchunked::send_ct::HeaderReceived`**
• The in-memory states that survive a round trip: `hdr` must be exactly 64 bytes long.
• Transcribed from the `#[hax_lib::refine(hdr.len() == 64)]` annotation on the Rust struct.
-/
def WellFormed (x : HeaderReceived) : Prop := x.hdr.length = 64

/-- **Round trip `fromPb ∘ intoPb` (RT1) for
`spqr::v1::unchunked::send_ct::serialize::HeaderReceived`**
• Every well-formed in-memory state survives encoding followed by decoding unchanged. -/
@[simp]
theorem roundtrip_fromPb_intoPb (x : HeaderReceived) (h : WellFormed x) :
    fromPb (intoPb x) = .Ok x := by
  unfold WellFormed at h
  unfold fromPb intoPb
  rw [h]
  rfl

/-- **Successfully decoded protobuf input states yield well-formed in-memory states (RT2a) for
`spqr::v1::unchunked::send_ct::serialize::HeaderReceived`**
• Every in-memory state the decoder successfully produces satisfies `WellFormed`. -/
theorem wellFormed_of_fromPb (pb : v1_state.unchunked.HeaderReceived) (x : HeaderReceived)
    (h : fromPb pb = .Ok x) : WellFormed x := by
  unfold fromPb at h
  split at h
  · simp only [core.result.Result.Ok.injEq] at h
    subst h
    assumption
  · simp only [reduceCtorEq] at h

/-- **Round trip `intoPb ∘ fromPb` (RT2b) for
`spqr::v1::unchunked::send_ct::serialize::HeaderReceived`**
• Every successfully decoded protobuf state is the encoding of the in-memory state it
  decodes to. -/
theorem roundtrip_intoPb_fromPb (pb : v1_state.unchunked.HeaderReceived) (x : HeaderReceived)
    (h : fromPb pb = .Ok x) : intoPb x = pb := by
  rcases pb with ⟨epoch, auth, hdr⟩
  unfold fromPb at h
  split at h
  next a ha _ =>
    simp only [core.result.Result.Ok.injEq] at h
    subst h ha
    rw [intoPb, Authenticator.FunctionalModels.roundtrip_intoPb_fromPb a]
  next => simp only [reduceCtorEq] at h

end spqr.v1.unchunked.send_ct.serialize.HeaderReceived.FunctionalModels
