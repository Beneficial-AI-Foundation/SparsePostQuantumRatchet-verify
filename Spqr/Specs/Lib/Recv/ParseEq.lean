/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import SrcTranslated.Funs

/-!
# `spqr::recv` depends on the message only through its parse

`recv` reads the message bytes only through `msg_preamble` (version, epoch, index and the
remaining bytes) and, on the version-1 path, through `Message::deserialize` of the remaining
bytes. So two byte strings with the same parsed version, epoch and index, whose remaining
bytes deserialize to the same result, are indistinguishable to `recv`: from any state, `recv`
returns the same result on both.

The wire format is not injective (`Message.serialize_parse_not_injective`), so the extra
encodings cannot change what `recv` returns. A caller that inspects the raw bytes can still
tell them apart.

**Source**: src/lib.rs (lines 361:0-490:1)
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr

/-- If two messages have preambles with the same version, epoch and index, and their remaining
bytes deserialize to the same result, then `recv` returns the same result on both, from any
state. -/
theorem recv_eq_of_parse_eq (state b₁ b₂ : alloc.vec.Vec Std.U8) (p₁ p₂ : MsgPreamble)
    (h₁ : msg_preamble b₁ = ok (.Ok p₁)) (h₂ : msg_preamble b₂ = ok (.Ok p₂))
    (hv : p₁.version = p₂.version) (he : p₁.epoch = p₂.epoch) (hi : p₁.index = p₂.index)
    (hd : v1.chunked.states.serialize.Message.deserialize p₁.epoch p₁.remaining =
      v1.chunked.states.serialize.Message.deserialize p₂.epoch p₂.remaining) :
    recv state b₁ = recv state b₂ := by
  obtain ⟨v₁, e₁, i₁, r₁⟩ := p₁
  obtain ⟨v₂, e₂, i₂, r₂⟩ := p₂
  simp only at hv he hi hd
  subst hv he hi
  unfold recv
  rw [h₁, h₂]
  simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, hd]

end spqr
