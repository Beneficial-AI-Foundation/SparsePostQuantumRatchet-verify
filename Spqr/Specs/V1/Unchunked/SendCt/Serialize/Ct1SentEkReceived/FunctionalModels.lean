/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
module

public import SrcTranslated.Types
public import Spqr.Specs.Authenticator.Serialize.Authenticator.FunctionalModels

/-!
# Functional models of
`spqr::v1::unchunked::send_ct::serialize::Ct1SentEkReceived::{into_pb, from_pb}`

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

**Source**: spqr/src/v1/unchunked/send_ct/serialize.rs
-/

@[expose] public section

open Aeneas.Std spqr.proto.pq_ratchet spqr.authenticator.serialize
namespace spqr.v1.unchunked.send_ct.serialize.Ct1SentEkReceived.FunctionalModels

/-- **Functional model of `spqr::v1::unchunked::send_ct::serialize::Ct1SentEkReceived::into_pb`**
• A pure, total, human-readable function on the translated data types.
• Delegates to `Authenticator.FunctionalModels.intoPb` and wraps the result in `some`.
-/
def intoPb (x : Ct1SentEkReceived) : v1_state.unchunked.Ct1SentEkReceived :=
  { epoch := x.epoch, auth := some (Authenticator.FunctionalModels.intoPb x.auth), es := x.es,
    ek := x.ek, ct1 := x.ct1 }

/-- **Functional model of `spqr::v1::unchunked::send_ct::serialize::Ct1SentEkReceived::from_pb`**
• A pure, total, human-readable function on the translated data types.
• Delegates to `Authenticator.FunctionalModels.fromPb`; an `es` that is not 2080 bytes long, a
  `ct1` that is not 960 bytes long, an `ek` that is not 1152 bytes long or an absent `auth` is
  `Error.StateDecode`.
-/
def fromPb (pb : v1_state.unchunked.Ct1SentEkReceived) :
    core.result.Result Ct1SentEkReceived Error :=
  match pb.auth, pb.es.length, pb.ct1.length, pb.ek.length with
  | some a, 2080, 960, 1152 =>
    .Ok { epoch := pb.epoch, auth := Authenticator.FunctionalModels.fromPb a, es := pb.es,
          ek := pb.ek, ct1 := pb.ct1 }
  | _, _, _, _ => .Err Error.StateDecode

/-- **Well-formedness predicate for `spqr::v1::unchunked::send_ct::Ct1SentEkReceived`**
• The in-memory states that survive a round trip: `es` must be exactly 2080 bytes long, `ek` must
  be exactly 1152 bytes long and `ct1` must be exactly 960 bytes long.
• Transcribed from the `#[hax_lib::refine(es.len() == 2080)]`,
  `#[hax_lib::refine(ek.len() == 1152)]` and `#[hax_lib::refine(ct1.len() == 960)]` annotations on
  the Rust struct.
-/
def WellFormed (x : Ct1SentEkReceived) : Prop :=
  x.es.length = 2080 ∧ x.ek.length = 1152 ∧ x.ct1.length = 960

/-- **Round trip `fromPb ∘ intoPb` (RT1) for
`spqr::v1::unchunked::send_ct::serialize::Ct1SentEkReceived`**
• Every well-formed in-memory state survives encoding followed by decoding unchanged. -/
@[simp]
theorem roundtrip_fromPb_intoPb (x : Ct1SentEkReceived) (h : WellFormed x) :
    fromPb (intoPb x) = .Ok x := by
  unfold WellFormed at h
  obtain ⟨h1, h2, h3⟩ := h
  unfold fromPb intoPb
  rw [h1, h2, h3]
  rfl

/-- **Successfully decoded protobuf input states yield well-formed in-memory states (RT2a) for
`spqr::v1::unchunked::send_ct::serialize::Ct1SentEkReceived`**
• Every in-memory state the decoder successfully produces satisfies `WellFormed`. -/
theorem wellFormed_of_fromPb (pb : v1_state.unchunked.Ct1SentEkReceived) (x : Ct1SentEkReceived)
    (h : fromPb pb = .Ok x) : WellFormed x := by
  unfold fromPb at h
  split at h
  · simp only [core.result.Result.Ok.injEq] at h
    subst h
    exact ⟨‹_›, ‹_›, ‹_›⟩
  · simp only [reduceCtorEq] at h

/-- **Round trip `intoPb ∘ fromPb` (RT2b) for
`spqr::v1::unchunked::send_ct::serialize::Ct1SentEkReceived`**
• Every successfully decoded protobuf state is the encoding of the in-memory state it
  decodes to. -/
theorem roundtrip_intoPb_fromPb (pb : v1_state.unchunked.Ct1SentEkReceived) (x : Ct1SentEkReceived)
    (h : fromPb pb = .Ok x) : intoPb x = pb := by
  rcases pb with ⟨epoch, auth, es, ek, ct1⟩
  unfold fromPb at h
  split at h
  next a ha _ _ _ =>
    simp only [core.result.Result.Ok.injEq] at h
    subst h ha
    rw [intoPb, Authenticator.FunctionalModels.roundtrip_intoPb_fromPb a]
  next => simp only [reduceCtorEq] at h

end spqr.v1.unchunked.send_ct.serialize.Ct1SentEkReceived.FunctionalModels
