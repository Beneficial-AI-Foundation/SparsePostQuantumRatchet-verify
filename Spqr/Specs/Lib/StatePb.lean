/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
module

public import SrcTranslated.Funs
public import Spqr.Auxiliary.Aeneas.SpecImpExists

/-!
# Spec axioms for `spqr::encode_state_pb` and `spqr::decode_state_pb`

The two wrappers around prost's `encode_to_vec`/`decode` for `PqRatchetState` (added by the
translation patch `lib-state_pb.patch`) are opaque in the translation. The axioms below are the
trusted interface: encoding always succeeds, decoding never panics (it may return
`Err DecodeError`), and decoding an encoding gives back the encoded state.

Protobuf encoding is not canonical (unknown fields are dropped, fields may repeat or come in any
order, varints may be padded), so re-encoding a decoded state need not give back the input bytes;
nothing here claims that.

Source: "spqr/src/lib.rs"
-/

@[expose] public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace spqr

/-- `st` is the ratchet state that prost decodes from `bytes`. -/
def decodesTo (bytes : alloc.vec.Vec U8) (st : proto.pq_ratchet.PqRatchetState) : Prop :=
  ∀ s : Slice U8, s.val = bytes.val → decode_state_pb s = ok (.Ok st)

/-- **Spec axiom for `spqr::encode_state_pb`**
• Encoding the ratchet state succeeds.
• The bytes decode back to the encoded state. -/
@[step]
axiom encode_state_pb_spec (st : proto.pq_ratchet.PqRatchetState) :
    encode_state_pb st ⦃ (bytes : alloc.vec.Vec U8) => decodesTo bytes st ⦄

/-- **Spec axiom for `spqr::decode_state_pb`**
• Decoding never panics; malformed input gives `Err DecodeError`. -/
axiom decode_state_pb_total (s : Slice U8) : decode_state_pb s ⦃ _ => True ⦄

/-- **Spec theorem for `spqr::decode_state_pb`**
• Decoding never panics; the result is whatever prost decodes from the bytes of `s`. -/
@[step]
theorem decode_state_pb_spec (s : Slice U8) :
    decode_state_pb s ⦃ r => ∀ s' : Slice U8, s'.val = s.val → decode_state_pb s' = ok r ⦄ := by
  obtain ⟨r, h, -⟩ := WP.spec_imp_exists (decode_state_pb_total s)
  rw [h, spec_ok]
  intro s' hs'
  rw [Slice.ext s' s hs', h]

end spqr
