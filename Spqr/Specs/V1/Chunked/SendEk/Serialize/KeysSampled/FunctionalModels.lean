/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
module

public import SrcTranslated.Types
public import Spqr.Specs.V1.Unchunked.SendEk.Serialize.HeaderSent.FunctionalModels
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.FunctionalModels

/-!
# Functional models of `spqr::v1::chunked::send_ek::serialize::KeysSampled::{into_pb, from_pb}`

Pure, total Lean functions stating what the two Rust serializers compute, written against the
translated data types only, together with the well-formedness predicate and the round-trip laws
relating them. The spec theorems in `IntoPb.lean` and `FromPb.lean` pin the extracted, monadic
functions to these models. The nested components are handled by calling their own functional
models: `uc` via the unchunked `HeaderSent.FunctionalModels` and `sending_hdr` via
`PolyEncoder.FunctionalModels`.

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

**Source**: spqr/src/v1/chunked/send_ek/serialize.rs
-/

@[expose] public section

open Aeneas.Std spqr.proto.pq_ratchet spqr.encoding.polynomial spqr.v1.unchunked.send_ek.serialize
namespace spqr.v1.chunked.send_ek.serialize.KeysSampled.FunctionalModels

/-- **Functional model of `spqr::v1::chunked::send_ek::serialize::KeysSampled::into_pb`**
• A pure, total, human-readable function on the translated data types.
• Delegates to `HeaderSent.FunctionalModels.intoPb` for `uc` and to
  `PolyEncoder.FunctionalModels.intoPb` for `sending_hdr`, and wraps both results in `some`.
-/
def intoPb (x : KeysSampled) : v1_state.chunked.KeysSampled :=
  { uc := some (HeaderSent.FunctionalModels.intoPb x.uc),
    sending_hdr := some (PolyEncoder.FunctionalModels.intoPb x.sending_hdr) }

/-- **Functional model of `spqr::v1::chunked::send_ek::serialize::KeysSampled::from_pb`**
• A pure, total, human-readable function on the translated data types.
• Delegates to `HeaderSent.FunctionalModels.fromPb` for `uc` and to
  `PolyEncoder.FunctionalModels.fromPb` for `sending_hdr`; an absent or invalid `uc` or an
  absent or invalid `sending_hdr` is `Error.StateDecode`.
-/
def fromPb (pb : v1_state.chunked.KeysSampled) :
    core.result.Result KeysSampled Error :=
  match Option.map HeaderSent.FunctionalModels.fromPb pb.uc,
    Option.map PolyEncoder.FunctionalModels.fromPb pb.sending_hdr with
  | some (.Ok uc), some (.Ok sending_hdr) => .Ok { uc, sending_hdr }
  | _, _ => .Err Error.StateDecode

/-- **Well-formedness predicate for `spqr::v1::chunked::send_ek::KeysSampled`**
• The in-memory states that survive a round trip: `uc` must be well-formed as an unchunked
  `HeaderSent` and `sending_hdr` must be well-formed as a `PolyEncoder`.
• `KeysSampled` carries no refine annotation of its own, so the conjuncts are exactly the
  components' own `WellFormed` predicates.
-/
def WellFormed (x : KeysSampled) : Prop :=
  HeaderSent.FunctionalModels.WellFormed x.uc ∧
    PolyEncoder.FunctionalModels.WellFormed x.sending_hdr

/-- **Round trip `fromPb ∘ intoPb` (RT1) for
`spqr::v1::chunked::send_ek::serialize::KeysSampled`**
• Every well-formed in-memory state survives encoding followed by decoding unchanged. -/
@[simp]
theorem roundtrip_fromPb_intoPb (x : KeysSampled) (h : WellFormed x) :
    fromPb (intoPb x) = .Ok x := by
  obtain ⟨huc, henc⟩ := h
  unfold fromPb intoPb
  simp only [Option.map_some, HeaderSent.FunctionalModels.roundtrip_fromPb_intoPb x.uc huc,
    PolyEncoder.FunctionalModels.roundtrip_fromPb_intoPb x.sending_hdr henc]

/-- **Successfully decoded protobuf input states yield well-formed in-memory states (RT2a) for
`spqr::v1::chunked::send_ek::serialize::KeysSampled`**
• Every in-memory state the decoder successfully produces satisfies `WellFormed`. -/
theorem wellFormed_of_fromPb (pb : v1_state.chunked.KeysSampled) (x : KeysSampled)
    (h : fromPb pb = .Ok x) : WellFormed x := by
  unfold fromPb at h
  split at h
  next uc enc huc henc =>
    simp only [core.result.Result.Ok.injEq] at h
    subst h
    rcases pb with ⟨_ | u, _ | p⟩
    all_goals simp only [Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq]
      at huc henc
    exact ⟨HeaderSent.FunctionalModels.wellFormed_of_fromPb u uc huc,
      PolyEncoder.FunctionalModels.wellFormed_of_fromPb p enc henc⟩
  next => simp only [reduceCtorEq] at h

/-- **Round trip `intoPb ∘ fromPb` (RT2b) for
`spqr::v1::chunked::send_ek::serialize::KeysSampled`**
• Every successfully decoded protobuf state is the encoding of the in-memory state it
  decodes to. -/
theorem roundtrip_intoPb_fromPb (pb : v1_state.chunked.KeysSampled) (x : KeysSampled)
    (h : fromPb pb = .Ok x) : intoPb x = pb := by
  unfold fromPb at h
  split at h
  next uc enc huc henc =>
    simp only [core.result.Result.Ok.injEq] at h
    subst h
    rcases pb with ⟨_ | u, _ | p⟩
    all_goals simp only [Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq]
      at huc henc
    rw [intoPb, HeaderSent.FunctionalModels.roundtrip_intoPb_fromPb u uc huc,
      PolyEncoder.FunctionalModels.roundtrip_intoPb_fromPb p enc henc]
  next => simp only [reduceCtorEq] at h

end spqr.v1.chunked.send_ek.serialize.KeysSampled.FunctionalModels
