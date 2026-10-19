/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
/-! # Spec theorem for `spqr::{impl TryFrom<u8, String> for Version}::try_from`

Converts `u8` to `Version`: `0 → V0`, `1 → V1`, else
`Err(format!("Expected 0 or 1, got {value}"))`.

The error string is built with `format!`, i.e. the external `alloc::fmt::format`, which is
modelled as an `opaque` function in `SrcTranslated/FunsExternal.lean`. Its content is not
specified, so the spec below only states that the result is *some* `Err`. To show that the call
succeeds we use the trusted spec axiom `alloc.fmt.format_spec` in `SrcTranslated/FunsExternal.lean`
(formatting into a fresh `String` never fails, short of allocation failure, which Aeneas does not
model).

**Source**: spqr/src/lib.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.Version.Insts.CoreConvertTryFromU8String

/-- **Spec theorem for `spqr.proto.pq_ratchet.Version.Insts.CoreConvertTryFromU8String.try_from`**:

Maps `0 ↔ Ok V0`, `1 ↔ Ok V1`, `otherwise ↔ Err _` (the error message is produced by the
opaque `alloc.fmt.format`, so its content is left unspecified). No panic; errors via
`core.result.Result.Err`. -/
@[step]
theorem try_from_spec (value : U8) :
    try_from value ⦃ (result : core.result.Result proto.pq_ratchet.Version String) =>
      (value = 0#u8 ↔ result = core.result.Result.Ok proto.pq_ratchet.Version.V0) ∧
      (value = 1#u8 ↔ result = core.result.Result.Ok proto.pq_ratchet.Version.V1) ∧
      ((value ≠ 0#u8 ∧ value ≠ 1#u8) ↔ ∃ e, result = core.result.Result.Err e) ⦄ := by
  unfold try_from
  split
  · simp only [ne_eq, UScalar.neq_to_neq_val, UScalar.ofNatCore_val_eq, WP.spec_ok, iff_true,
      core.result.Result.Ok.injEq, reduceCtorEq, iff_false, exists_const, not_and,
      Decidable.not_not]
    decide
  · simp only [ne_eq, UScalar.neq_to_neq_val, UScalar.ofNatCore_val_eq, WP.spec_ok,
      core.result.Result.Ok.injEq, reduceCtorEq, iff_false, iff_true, exists_const, not_and,
      Decidable.not_not]
    decide
  · rename_i h0 h1
    have hv0 : value.val ≠ 0 := fun h => h0 (UScalar.eq_of_val_eq h)
    have hv1 : value.val ≠ 1 := fun h => h1 (UScalar.eq_of_val_eq h)
    simp only [core.fmt.rt.Argument.new_display, core.fmt.Arguments.new, core.hint.must_use,
      bind_ok]
    step*
    simp [hv0, hv1]

end spqr.proto.pq_ratchet.Version.Insts.CoreConvertTryFromU8String
