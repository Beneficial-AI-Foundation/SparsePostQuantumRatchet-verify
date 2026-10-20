/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs

/-!
# Spec theorems for `core::fmt::Arguments::from_str` and friends

In Rust's standard library, `core::fmt::Arguments::from_str` builds a `fmt::Arguments` value from
a string literal.  This is used in `format_args!` and `assert!` macros to produce the error
message argument.

The Aeneas-extracted Lean function `core.fmt.Arguments.from_str` always succeeds (returns `ok`).

**Source**: core/src/fmt/mod.rs (Arguments::from_str)
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.core.fmt.Arguments

/--
**Spec theorem for `core.fmt.Arguments.from_str`**:

The `from_str` function always succeeds (returns `ok`).  This is the Lean model for
`core::fmt::Arguments::from_str` which builds a format argument from a string literal.

**Source**: core/src/fmt/mod.rs (Arguments::from_str)
-/
@[step]
theorem from_str_spec (s : Str) :
    core.fmt.Arguments.from_str s
      ⦃ (_ : core.fmt.Arguments) => True ⦄ := by
  unfold core.fmt.Arguments.from_str
  exact (WP.spec_ok _).mpr trivial

/--
**Spec theorem for `core.fmt.Arguments.new`**: always succeeds. The Aeneas model ignores its
arguments and returns `()`.

`core.fmt.Arguments` is a plain `def` equal to `Unit`, so after unfolding, `simp`/`step` cannot
see that `ok ()` has the right type; these specs let proofs step over the call instead.

**Source**: core/src/fmt/mod.rs (Arguments::new)
-/
@[step]
theorem new_spec {N M : Usize} (pieces : Array U8 N) (args : Array core.fmt.rt.Argument M) :
    core.fmt.Arguments.new pieces args ⦃ (_ : core.fmt.Arguments) => True ⦄ := by
  unfold core.fmt.Arguments.new
  exact (WP.spec_ok _).mpr trivial

end Aeneas.Std.core.fmt.Arguments

namespace Aeneas.Std.core.fmt.rt.Argument

/--
**Spec theorem for `core.fmt.rt.Argument.new_display`**: always succeeds. The Aeneas model
ignores its arguments and returns `()`.

**Source**: core/src/fmt/rt.rs (Argument::new_display)
-/
@[step]
theorem new_display_spec {T : Type} (inst : core.fmt.Display T) (x : T) :
    core.fmt.rt.Argument.new_display inst x ⦃ (_ : core.fmt.rt.Argument) => True ⦄ := by
  unfold core.fmt.rt.Argument.new_display
  exact (WP.spec_ok _).mpr trivial

end Aeneas.Std.core.fmt.rt.Argument
