/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.EncodeBytes

/-! # Spec theorems for `spqr::encoding::{Encoder for Option<T>}::encode_bytes`

The `Option<T>` encoder wraps the inner `T` encoder: successes are tagged with `Some`, errors
pass through unchanged.

Two theorems:
  • `encode_bytes_spec_lift` — lifts any postcondition of the inner encoder through the wrapper.
  • `encode_bytes_spec_poly_encoder` — instantiates the lift for `T = PolyEncoder`.

**Source**: spqr/src/encoding.rs -/

open Aeneas Aeneas.Std Result spqr encoding.polynomial

namespace spqr.core.option.Option.Insts.SpqrEncodingEncoder

/-- **Predicate-lifting spec for `Option<T>::encode_bytes`**:

If the inner encoder satisfies `P`, then the wrapped encoder satisfies `P` relabelled through
`Option`: `Ok (some val) ↦ P (Ok val)`, `Err e ↦ P (Err e)`, `Ok none ↦ False`. -/
@[step]
theorem encode_bytes_spec_lift
    {T : Type} (EncoderInst : encoding.Encoder T) (msg : Slice Std.U8)
    (P : core.result.Result T encoding.EncodingError → Prop)
    (h_inner :
        EncoderInst.encode_bytes msg ⦃ (r : core.result.Result T encoding.EncodingError) =>
          P r ⦄) :
    encode_bytes EncoderInst msg ⦃
        (result : core.result.Result (Option T) encoding.EncodingError) =>
      match result with
      | core.result.Result.Ok (some val) => P (core.result.Result.Ok val)
      | core.result.Result.Err e => P (core.result.Result.Err e)
      | _ => False ⦄ := by
  unfold encode_bytes
  step with h_inner
  cases r with
  | Ok val =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, WP.spec_ok]
    assumption
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from, WP.spec_ok]
    assumption

/-- **`encode_bytes` spec for `Option<PolyEncoder>`**:

Instantiates `encode_bytes_spec_lift` with the `PolyEncoder` postcondition. Given `h_even` and
`h_len`, the result is `Ok (some ⟨0#u32, Points pts⟩)` where each `pts[j]` has the expected
round-robin length and coefficients matching big-endian byte pairs from `msg`. -/
@[step]
theorem encode_bytes_spec_poly_encoder
    (msg : Slice U8)
    (h_even : msg.length % 2 = 0)
    (h_len : msg.length ≤ 2 ^ 16 * 16) :
    encode_bytes PolyEncoder.Insts.SpqrEncodingEncoder msg ⦃
        (result : core.result.Result (Option PolyEncoder) encoding.EncodingError) =>
      match result with
      | core.result.Result.Ok (some ⟨idx, EncoderState.Points pts⟩) =>
        idx = 0#u32 ∧
        (∀ (j : Nat), j < 16 →
          pts[j]!.value.length =
            if j < (msg.length / 2) % 16
            then msg.length / 2 / 16 + 1
            else msg.length / 2 / 16) ∧
        (∀ (j : Nat), j < 16 →
          ∀ (k : Nat), k < pts[j]!.value.length →
            2 * (j + 16 * k) + 1 < msg.length ∧
            (listToGF216Poly pts[j]!.value).coeff k =
              (256 * msg[2 * (j + 16 * k)]! + (msg[2 * (j + 16 * k) + 1]!).val).toGF216)
      | _ => False ⦄ := by
  have h_inner := PolyEncoder.Insts.SpqrEncodingEncoder.encode_bytes_spec msg h_even h_len
  unfold encode_bytes
  step with h_inner
  cases r with
  | Ok val =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, WP.spec_ok]
    obtain ⟨idx, s⟩ := val
    cases s <;> assumption
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from, WP.spec_ok]
    assumption

end spqr.core.option.Option.Insts.SpqrEncodingEncoder
