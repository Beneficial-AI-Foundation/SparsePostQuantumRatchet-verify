/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
import SrcTranslated.Types
import Spqr.Specs.V1.Unchunked.SendEk.Serialize.KeysUnsampled.FunctionalModels

/-!
# Functional models of `spqr::v1::chunked::send_ek::serialize::KeysUnsampled::{into_pb, from_pb}`

Pure, total Lean functions stating what the two Rust serializers compute, written against the
translated data types only, together with the round-trip laws relating them. The spec theorems
in `IntoPb.lean` and `FromPb.lean` pin the extracted, monadic functions to these models. The
chunked state wraps a single unchunked field `uc`, which is handled by calling the functional
model of the unchunked `KeysUnsampled`.

**Source**: spqr/src/v1/chunked/send_ek/serialize.rs
-/

open Aeneas.Std spqr.proto.pq_ratchet
open spqr.v1.unchunked.send_ek.serialize.KeysUnsampled.FunctionalModels
  renaming intoPb → Unchunked.intoPb, fromPb → Unchunked.fromPb,
    roundtrip_intoPb_fromPb → Unchunked.roundtrip_intoPb_fromPb
namespace spqr.v1.chunked.send_ek.serialize.KeysUnsampled.FunctionalModels

/-- **Functional model of `spqr::v1::chunked::send_ek::serialize::KeysUnsampled::into_pb`**
• A pure, total, human-readable function on the translated data types.
• Serializes the inner unchunked state with `Unchunked.intoPb` and wraps it in `some`.
-/
def intoPb (x : KeysUnsampled) : v1_state.chunked.KeysUnsampled :=
  { uc := some (Unchunked.intoPb x.uc) }

/-- **Functional model of `spqr::v1::chunked::send_ek::serialize::KeysUnsampled::from_pb`**
• A pure, total, human-readable function on the translated data types.
• Decodes the inner state via `Unchunked.fromPb`; absent or invalid input is `Error.StateDecode`.
-/
def fromPb (pb : v1_state.chunked.KeysUnsampled) :
    core.result.Result KeysUnsampled Error :=
  match Option.map Unchunked.fromPb pb.uc with
  | some (.Ok uc) => .Ok { uc := uc }
  | _             => .Err Error.StateDecode

/-- **Round trip `fromPb ∘ intoPb` for `spqr::v1::chunked::send_ek::serialize::KeysUnsampled`** -/
@[simp]
theorem roundtrip_fromPb_intoPb (x : KeysUnsampled) : fromPb (intoPb x) = .Ok x := rfl

/-- **Round trip `intoPb ∘ fromPb` for `spqr::v1::chunked::send_ek::serialize::KeysUnsampled`** -/
theorem roundtrip_intoPb_fromPb (pb : v1_state.chunked.KeysUnsampled) (x : KeysUnsampled)
    (h : fromPb pb = .Ok x) : intoPb x = pb := by
  rcases pb with ⟨_ | u⟩
  · simp [fromPb] at h
  · rcases hu : Unchunked.fromPb u with uc | _
    · simp only [fromPb, Option.map_some, hu, core.result.Result.Ok.injEq] at h
      rw [intoPb, ← h, Unchunked.roundtrip_intoPb_fromPb u uc hu]
    · simp [fromPb, hu] at h

end spqr.v1.chunked.send_ek.serialize.KeysUnsampled.FunctionalModels
