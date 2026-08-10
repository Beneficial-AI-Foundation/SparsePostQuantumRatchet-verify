/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `spqr::{impl core::fmt::Debug for spqr::SecretOutput}::fmt`

Structural `Debug` formatter for `SecretOutput ≃ None ⊕ Send(Vec<u8>) ⊕ Recv(Vec<u8>)`.
Dispatches on the constructor: `None` uses `write_str`, `Send`/`Recv` use
`debug_tuple_field1_finish`. Under the Aeneas `core::fmt` model all branches return
`(.Ok (), f)`, so formatting always succeeds and preserves the formatter state.

**Source**: spqr/src/lib.rs -/

open Aeneas Aeneas.Std Result

namespace spqr.SecretOutput.Insts.CoreFmtDebug

/--
**Spec theorem for `spqr.SecretOutput.Insts.CoreFmtDebug.fmt`**:

• Takes a `SecretOutput` value `self` and a `core.fmt.Formatter` value `f`.
• Pattern-matches on the variant of `self`:
  - `None` → delegates to `Formatter.write_str f "None"`
  - `Send(v)` → wraps `v` in `Dyn.mk _ (DebugShared (DebugVec DebugU8))` and delegates to
    `Formatter.debug_tuple_field1_finish f "Send"`
  - `Recv(v)` → wraps `v` in `Dyn.mk _ (DebugShared (DebugVec DebugU8))` and delegates to
    `Formatter.debug_tuple_field1_finish f "Recv"`
• Returns a pair `(core.result.Result Unit core.fmt.Error) × core.fmt.Formatter`.

• The function always succeeds (no panic) for any `SecretOutput` input and any `Formatter` state.

The result satisfies the formatting postcondition:

  `result.1 = .Ok ()  ∧  result.2 = f`

i.e. the debug formatting succeeds with `Ok(())` and the formatter is returned unchanged
(under the current Aeneas simplistic model of the `core::fmt` machinery). -/
@[step]
theorem fmt_spec (self : spqr.SecretOutput) (f : core.fmt.Formatter) :
    fmt self f ⦃ (result : (core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) =>
      result.1 = .Ok () ∧ result.2 = f ⦄ := by
  unfold fmt
  match self with
  | .None =>
    simp only [core.fmt.Formatter.write_str]
    step*
  | .Send _ =>
    simp only [core.fmt.Formatter.debug_tuple_field1_finish]
    step*
  | .Recv _ =>
    simp only [core.fmt.Formatter.debug_tuple_field1_finish]
    step*

end spqr.SecretOutput.Insts.CoreFmtDebug
