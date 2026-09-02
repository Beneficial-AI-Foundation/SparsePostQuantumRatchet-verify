/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs

/-! # Spec theorem for
`spqr::serialize::{impl core::fmt::Display for spqr::serialize::Error}::fmt`

The `thiserror`-derived `Display` for the fieldless enum `serialize::Error` dispatches on
the constructor and writes the `#[error("...")]` message with `Formatter::write_str`:

- `Deserialization` → `"General deserialization error"`
- `EncodingDecoding` → `"Error with encoder/decoder serialization"`

Under the Aeneas `core::fmt` model `write_str` always returns `(.Ok (), f)`, so
formatting always succeeds and preserves the formatter state.

**Source**: src/serialize.rs (lines 6-12, `#[derive(thiserror::Error)]` + `#[error(...)]`)
-/

open Aeneas Aeneas.Std Result

namespace spqr.serialize.Error.Insts.CoreFmtDisplay

/-- **Spec theorem for `serialize.Error.Insts.CoreFmtDisplay.fmt`**:

The `Display for Error` implementation always succeeds (no panic) for any variant `self`
and any formatter `f`. It returns `Ok(())` and leaves the formatter unchanged (under the
current Aeneas model of the `core::fmt` machinery):

  `result.1 = .Ok ()  ∧  result.2 = f` -/
@[step]
theorem fmt_spec (self : serialize.Error) (f : core.fmt.Formatter) :
    fmt self f ⦃ (result : (core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) =>
      result.1 = .Ok () ∧ result.2 = f ⦄ := by
  unfold fmt
  match self with
  | .Deserialization =>
    simp only [core.fmt.Formatter.write_str]
    step*
  | .EncodingDecoding =>
    simp only [core.fmt.Formatter.write_str]
    step*

end spqr.serialize.Error.Insts.CoreFmtDisplay
