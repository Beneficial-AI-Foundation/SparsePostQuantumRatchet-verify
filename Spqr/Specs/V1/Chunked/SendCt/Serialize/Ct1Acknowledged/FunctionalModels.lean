/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
module

import SrcTranslated.Types
public import Spqr.Specs.V1.Unchunked.SendCt.Serialize.Ct1Sent.FunctionalModels
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.FunctionalModels

/-!
# Functional models of `spqr::v1::chunked::send_ct::serialize::Ct1Acknowledged::{into_pb, from_pb}`

Pure, total Lean functions stating what the two Rust serializers compute, written against the
translated data types only, together with the well-formedness and canonicity predicates and the
round-trip laws relating them. The spec theorems in `IntoPb.lean` and `FromPb.lean` pin the
extracted, monadic functions to these models. The nested components are handled by calling their own
functional models: `uc` via the unchunked `Ct1Sent.FunctionalModels` and `receiving_ek` via
`PolyDecoder.FunctionalModels`.

Several protobuf states can decode to the same in-memory state, because decoding `receiving_ek` is
lenient (see `PolyDecoder.FunctionalModels`). Encoding that state gives back only one of them, and
`Canonical` holds for exactly that one.

The round-trip laws are four separate theorems. The RT1 laws start from an in-memory state and the
RT2 laws from a protobuf state. Each `a` law says where one model sends its inputs, and each `b` law
describes a round trip.

• `canonical_intoPb` (RT1a): every well-formed in-memory state encodes to a canonical protobuf
  state.

• `roundtrip_fromPb_intoPb` (RT1b): every well-formed in-memory state survives encoding followed by
  decoding unchanged.

• `wellFormed_of_fromPb` (RT2a): every protobuf state the decoder successfully decodes yields a
  well-formed in-memory state.

• `roundtrip_intoPb_fromPb` (RT2b): every canonical protobuf state survives decoding followed by
  encoding unchanged.

Together, RT1a and RT2a say that `intoPb` sends well-formed in-memory states to canonical protobuf
states and that `fromPb` sends every protobuf state it decodes to a well-formed in-memory state.
RT1b and RT2b say that `fromPb ∘ intoPb` is the identity on the well-formed in-memory states and
that `intoPb ∘ fromPb` is the identity on the canonical protobuf states.

**So `intoPb` and `fromPb` restrict to mutually inverse bijections between the well-formed in-memory
states and the canonical protobuf states.**

Moreover, `WellFormed` and `Canonical` characterise exactly the states that survive their respective
round trips: every in-memory state that survives is well-formed by RT2a, and every protobuf state
that survives is canonical by RT2a and RT1a.

**Source**: spqr/src/v1/chunked/send_ct/serialize.rs
-/

@[expose] public section

open Aeneas.Std spqr.proto.pq_ratchet spqr.encoding.polynomial
namespace spqr.v1.chunked.send_ct.serialize.Ct1Acknowledged.FunctionalModels

/-- **Functional model of `spqr::v1::chunked::send_ct::serialize::Ct1Acknowledged::into_pb`**
• A pure, total, human-readable function on the translated data types.
• Delegates to the unchunked `Ct1Sent.FunctionalModels.intoPb` for `uc` and to
  `PolyDecoder.FunctionalModels.intoPb` for `receiving_ek`, and wraps both results in `some`.
-/
def intoPb (x : Ct1Acknowledged) : v1_state.chunked.Ct1Acknowledged :=
  { uc := some (unchunked.send_ct.serialize.Ct1Sent.FunctionalModels.intoPb x.uc),
    receiving_ek := some (PolyDecoder.FunctionalModels.intoPb x.receiving_ek) }

/-- **Functional model of `spqr::v1::chunked::send_ct::serialize::Ct1Acknowledged::from_pb`**
• A pure, total, human-readable function on the translated data types.
• A present `receiving_ek` whose `pts_needed` is not `576` (`ENCAPSULATION_KEY_SIZE / 2`) is
  `Error.MsgDecode`; `from_pb` checks this first.
• Otherwise delegates to the unchunked `Ct1Sent.FunctionalModels.fromPb` for `uc` and to
  `PolyDecoder.FunctionalModels.fromPb` for `receiving_ek`; an absent or invalid `uc` or an absent
  or invalid `receiving_ek` is `Error.StateDecode`.
-/
def fromPb (pb : v1_state.chunked.Ct1Acknowledged) :
    core.result.Result Ct1Acknowledged Error :=
  if ∃ d ∈ pb.receiving_ek, d.pts_needed.val ≠ 576 then .Err Error.MsgDecode else
  match Option.map unchunked.send_ct.serialize.Ct1Sent.FunctionalModels.fromPb pb.uc,
    Option.map PolyDecoder.FunctionalModels.fromPb pb.receiving_ek with
  | some (.Ok uc), some (.Ok receiving_ek) => .Ok { uc, receiving_ek }
  | _, _ => .Err Error.StateDecode

/-- **Well-formedness predicate for `spqr::v1::chunked::send_ct::Ct1Acknowledged`**
• The in-memory states that survive a round trip: `uc` must be well-formed as an unchunked `Ct1Sent`
  and `receiving_ek` must be well-formed as a `PolyDecoder`.
• `receiving_ek.pts_needed` is `576`, the struct's refine annotation (`ENCAPSULATION_KEY_SIZE / 2`),
  which `from_pb` checks.
-/
def WellFormed (x : Ct1Acknowledged) : Prop :=
  unchunked.send_ct.serialize.Ct1Sent.FunctionalModels.WellFormed x.uc ∧
    PolyDecoder.FunctionalModels.WellFormed x.receiving_ek ∧ x.receiving_ek.pts_needed.val = 576

/-- **Canonicity predicate for `spqr::v1::chunked::send_ct::Ct1Acknowledged`**
• The protobuf states that survive a round trip, that is, the encodings of well-formed states: among
  the protobuf states that decode to the same in-memory state, the one that encoding produces.
• `fromPb` decodes the state successfully (implicit requirement).
• The field `receiving_ek` is present, that is, `some d`, and the protobuf decoder `d` it holds
  satisfies `PolyDecoder.FunctionalModels.Canonical`: among the protobuf decoders that decode to the
  same in-memory `PolyDecoder`, `d` is the one that encoding produces.
-/
def Canonical (pb : v1_state.chunked.Ct1Acknowledged) : Prop :=
  (∃ x, fromPb pb = .Ok x) ∧
    ∃ d, pb.receiving_ek = some d ∧ PolyDecoder.FunctionalModels.Canonical d

/-- **Round trip `fromPb ∘ intoPb` (RT1b) for
`spqr::v1::chunked::send_ct::serialize::Ct1Acknowledged`**
• Every well-formed in-memory state survives encoding followed by decoding unchanged. -/
@[simp]
theorem roundtrip_fromPb_intoPb (x : Ct1Acknowledged) (h : WellFormed x) :
    fromPb (intoPb x) = .Ok x := by
  obtain ⟨huc, hdec, hn⟩ := h
  have hpts : (PolyDecoder.FunctionalModels.intoPb x.receiving_ek).pts_needed.val = 576 :=
    (UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (hn.trans_lt (by decide))).trans hn
  unfold fromPb intoPb
  simp only [Option.mem_def, Option.some.injEq, exists_eq_left', hpts, ne_eq, not_true_eq_false,
    ↓reduceIte, Option.map_some,
    unchunked.send_ct.serialize.Ct1Sent.FunctionalModels.roundtrip_fromPb_intoPb x.uc huc,
    PolyDecoder.FunctionalModels.roundtrip_fromPb_intoPb x.receiving_ek hdec]

/-- **Encoded well-formed in-memory states yield canonical protobuf states (RT1a) for
`spqr::v1::chunked::send_ct::serialize::Ct1Acknowledged`**
• Every well-formed in-memory state encodes to a canonical protobuf state. -/
theorem canonical_intoPb (x : Ct1Acknowledged) (h : WellFormed x) : Canonical (intoPb x) := by
  refine ⟨⟨x, roundtrip_fromPb_intoPb x h⟩, _, rfl, ?_⟩
  obtain ⟨-, hdec, -⟩ := h
  exact PolyDecoder.FunctionalModels.canonical_intoPb _ hdec

/-- **Successfully decoded protobuf input states yield well-formed in-memory states (RT2a) for
`spqr::v1::chunked::send_ct::serialize::Ct1Acknowledged`**
• Every in-memory state the decoder successfully produces satisfies `WellFormed`. -/
theorem wellFormed_of_fromPb (pb : v1_state.chunked.Ct1Acknowledged) (x : Ct1Acknowledged)
    (h : fromPb pb = .Ok x) : WellFormed x := by
  unfold fromPb at h
  split at h
  next => cases h
  rename_i hg
  split at h
  next uc dec huc hdec =>
    cases h
    obtain ⟨u, -, huc⟩ := Option.map_eq_some_iff.mp huc
    obtain ⟨p, hp, hdec⟩ := Option.map_eq_some_iff.mp hdec
    refine ⟨unchunked.send_ct.serialize.Ct1Sent.FunctionalModels.wellFormed_of_fromPb
      u uc huc, PolyDecoder.FunctionalModels.wellFormed_of_fromPb p dec hdec, ?_⟩
    have hn : p.pts_needed.val = 576 := Decidable.of_not_not fun hne => hg ⟨p, hp, hne⟩
    rcases dite_eq_iff.mp hdec with ⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩
    exact (U32.cast_Usize_val_eq _).trans hn
  next => cases h

/-- **Round trip `intoPb ∘ fromPb` (RT2b) for
`spqr::v1::chunked::send_ct::serialize::Ct1Acknowledged`**
• Every canonical protobuf state survives decoding followed by encoding unchanged. -/
theorem roundtrip_intoPb_fromPb (pb : v1_state.chunked.Ct1Acknowledged) (h : Canonical pb) :
    ∃ x, fromPb pb = .Ok x ∧ intoPb x = pb := by
  obtain ⟨⟨x, hx⟩, d, hd, hc⟩ := h
  refine ⟨x, hx, ?_⟩
  unfold fromPb at hx
  split at hx
  next => cases hx
  split at hx
  next uc dec huc hdec =>
    cases hx
    obtain ⟨u, hu, huc⟩ := Option.map_eq_some_iff.mp huc
    obtain ⟨p, hp, hdec⟩ := Option.map_eq_some_iff.mp hdec
    cases hd.symm.trans hp
    obtain ⟨y, hy, hyp⟩ := PolyDecoder.FunctionalModels.roundtrip_intoPb_fromPb _ hc
    cases hdec.symm.trans hy
    exact congrArg₂ v1_state.chunked.Ct1Acknowledged.mk
      ((congrArg some
        (unchunked.send_ct.serialize.Ct1Sent.FunctionalModels.roundtrip_intoPb_fromPb
          u uc huc)).trans hu.symm) ((congrArg some hyp).trans hp.symm)
  next => cases hx

end spqr.v1.chunked.send_ct.serialize.Ct1Acknowledged.FunctionalModels
