/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorems for `spqr::encoding::{Decoder for Option<T>}::decoded_message`

`Option<T>::decoded_message` unwraps `self` and delegates to `T::decoded_message`.
Extracted body: `as_ref` → `unwrap` → `DecoderInst.decoded_message`.

Theorem:
  • `decoded_message_spec_lift` — lifts a postcondition through the `Option<T>` wrapper.

The `PolyDecoder` instantiation takes the inner postcondition as a hypothesis since
`PolyDecoder.decoded_message` is an external axiom.

**Source**: spqr/src/encoding.rs (lines 94:4-100:5)
-/

open Aeneas Aeneas.Std Result spqr encoding.polynomial

namespace spqr.core.option.Option.Insts.SpqrEncodingDecoder

/-- **Predicate-lifting spec for `Option<T>::decoded_message`**:

Given a `Decoder T` instance `DecoderInst`, an option `self` with `self.isSome`, and a
predicate `P` on the decoded result, the hypothesis `h_inner` states that whenever
`self = some tmp` the inner call `DecoderInst.decoded_message tmp` satisfies `P`.
The theorem concludes that `decoded_message DecoderInst self` satisfies `P` directly,
since the `Option<T>` wrapper is structurally transparent for `decoded_message`.

The proof composes the functional steps of the extraction:

  1. `core.option.Option.as_ref` — transparent identity on `Option T`.
  2. `core.option.Option.unwrap` — partial projection, succeeding because `self.isSome`,
     producing `value` with `self = some value`.
  3. `DecoderInst.decoded_message value` — delegation to the inner decoder, discharged
     by `h_inner`. -/
@[step]
theorem decoded_message_spec_lift
    {T : Type} (DecoderInst : encoding.Decoder T) (self : Option T)
    (h_some : self.isSome)
    (P : Option (alloc.vec.Vec Std.U8) → Prop)
    (h_inner : ∀ tmp, self = some tmp →
        DecoderInst.decoded_message tmp ⦃ (r : Option (alloc.vec.Vec Std.U8)) => P r ⦄) :
    decoded_message DecoderInst self ⦃ (result : Option (alloc.vec.Vec Std.U8)) =>
      P result ⦄ := by
  unfold decoded_message
  simp only [core.option.Option.as_ref, bind_tc_ok]
  step with Aeneas.Std.core.option.Option.unwrap.spec as ⟨value, h_eq⟩
  exact h_inner value h_eq

end spqr.core.option.Option.Insts.SpqrEncodingDecoder
