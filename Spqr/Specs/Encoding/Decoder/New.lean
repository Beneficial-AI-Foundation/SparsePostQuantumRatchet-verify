/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.New

/-!
# Spec theorems for `spqr::encoding::{Decoder for Option<T>}::new`

The `Decoder` impl for `Option<T>` delegates to the inner `T::new`, wraps success in `Some`,
and forwards errors unchanged. After hax extraction the `?`-desugared body becomes:
`DecoderInst.new` → `Try.branch` → match on `Continue`/`Break`.

Two theorems:
  • `new_spec_lift` — lifts an arbitrary postcondition through the `Option<T>` wrapper.
  • `new_spec_poly_decoder` — the `T = PolyDecoder` instance via the lift.

**Source**: spqr/src/encoding.rs -/

open Aeneas Aeneas.Std Result spqr encoding.polynomial

namespace spqr.core.option.Option.Insts.SpqrEncodingDecoder

/-- **Predicate-lifting spec for `Option<T>::new`**:

Given `h_inner : DecoderInst.new len_bytes ⦃ P ⦄`, concludes that `new DecoderInst len_bytes`
satisfies: `Ok (some val) ↦ P (Ok val)`, `Err e ↦ P (Err e)`, `Ok none ↦ False`. -/
@[step]
theorem new_spec_lift
    {T : Type} (DecoderInst : encoding.Decoder T) (len_bytes : Std.Usize)
    (P : core.result.Result T encoding.EncodingError → Prop)
    (h_inner :
        DecoderInst.new len_bytes ⦃ (r : core.result.Result T encoding.EncodingError) =>
          P r ⦄) :
    new DecoderInst len_bytes ⦃ (result : core.result.Result (Option T) encoding.EncodingError) =>
      match result with
      | core.result.Result.Ok (some val) => P (core.result.Result.Ok val)
      | core.result.Result.Err e => P (core.result.Result.Err e)
      | _ => False ⦄ := by
  unfold new
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

/-- **`new` spec for `Option<PolyDecoder>`**:

Lifts `PolyDecoder.Insts.SpqrEncodingDecoder.new_spec` through `new_spec_lift`:
  • Even `len_bytes.val`: succeeds with `Ok (some pd)` where `pd.pts_needed = len_bytes/2`,
    `pd.pts` has 16 default entries, and `pd.is_complete = false`.
  • Odd `len_bytes.val`: returns `Err (PolynomialError MessageLengthEven)`. -/
@[step]
theorem new_spec_poly_decoder (len_bytes : Std.Usize) :
    new PolyDecoder.Insts.SpqrEncodingDecoder len_bytes ⦃
        (result : core.result.Result (Option PolyDecoder) encoding.EncodingError) =>
      if len_bytes.val % 2 = 0 then
        match result with
        | core.result.Result.Ok (some pd) =>
            pd.pts_needed = ⟨len_bytes.val / 2, by
                have : len_bytes.val / 2 ≤ len_bytes.val := Nat.div_le_self _ _
                exact Nat.lt_of_le_of_lt this len_bytes.hBounds⟩ ∧
            pd.pts.val = List.replicate 16 default ∧
            pd.is_complete = false
        | _ => False
      else
        result = core.result.Result.Err
          (encoding.EncodingError.PolynomialError
            encoding.polynomial.PolynomialError.MessageLengthEven) ⦄ := by
  have h := new_spec_lift PolyDecoder.Insts.SpqrEncodingDecoder len_bytes _
    (PolyDecoder.Insts.SpqrEncodingDecoder.new_spec len_bytes)
  apply WP.spec_mono h
  grind

end spqr.core.option.Option.Insts.SpqrEncodingDecoder
