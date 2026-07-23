/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs

/-! # Spec axiom for
`alloc::str::{alloc::borrow::ToOwned<str, alloc::string::String>}::to_owned`

In Rust, `str::to_owned` copies the bytes of a `&str` into a freshly allocated `String`
(`String::from_utf8_unchecked(self.as_bytes().to_owned())`). Semantically it never fails and
returns a string with exactly the same contents; its only failure mode is allocation failure,
which aborts the process instead of returning.

Aeneas models it as the opaque axiom
`Str.Insts.AllocBorrowToOwnedString.to_owned : Str → Result String` in
`SrcTranslated/FunsExternal.lean`, which carries no behavior, so the spec below must itself be
an axiom: on any `Str` built from a Lean `String` via `toStr`, the call succeeds and returns
that same string. This covers every call site in the extracted code, where the argument is
always `toStr <string literal>`.

The axiom is deliberately restricted to the image of `toStr` rather than stated for an
arbitrary `Str` (`:= Slice U8`): an arbitrary byte slice need not be valid UTF-8, and no Lean
`String` has such bytes, so the unrestricted statement would be unsatisfiable — an unsound
axiom. On the image of `toStr` it is consistent: UTF-8 encoding is injective, so `to_owned`
can be modeled as the partial inverse of `toStr`.

**Source**: alloc/src/str.rs, line 210 (`impl ToOwned for str`)
-/

open Aeneas Aeneas.Std Result

namespace Str.Insts.AllocBorrowToOwnedString

/-- **Spec axiom for `Str.Insts.AllocBorrowToOwnedString.to_owned`**:

On a string slice built from a Lean `String` by `toStr`, the call succeeds and returns that
same string (Rust's `str::to_owned` cannot fail: on allocation failure it aborts instead of
returning). -/
axiom to_owned_eq (s : String) (h : s.toByteArray.size ≤ U32.max) :
    to_owned (toStr s h) = ok s

/-- **Spec theorem for `Str.Insts.AllocBorrowToOwnedString.to_owned`** (derived from the spec
axiom `to_owned_eq`):

• On a string slice built from a Lean `String` by `toStr`, the call always succeeds.
• The resulting owned `String` has the same contents as the input slice. -/
@[step]
theorem to_owned_spec (s : String) (h : s.toByteArray.size ≤ U32.max) :
    to_owned (toStr s h) ⦃ (result : String) => result = s ⦄ := by
  simp only [to_owned_eq, WP.spec_ok]

end Str.Insts.AllocBorrowToOwnedString
