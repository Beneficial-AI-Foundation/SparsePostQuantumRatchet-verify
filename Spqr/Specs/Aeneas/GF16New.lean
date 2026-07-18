/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `spqr::encoding::gf::GF16::new`

In the spqr crate, `GF16::new(value: u16)` constructs a `GF16` field element by wrapping the
raw `u16` value.  The resulting `GF16` has `result.value = value`.

The Aeneas-extracted Lean function `encoding.gf.GF16.new` mirrors this behavior.

This specification is used in deserialization code (e.g. `Poly::deserialize`,
`PolyEncoder::from_pb`) where `GF16::new(u16::from_be_bytes(...))` reconstructs field elements
from their byte representation.

**Source**: spqr/src/encoding/gf.rs (GF16::new)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.gf.GF16

/--
**Spec theorem for `encoding.gf.GF16.new`**:

`GF16::new value` always succeeds and produces a `GF16` whose underlying `u16` field is exactly
`value`.

**Source**: spqr/src/encoding/gf.rs (GF16::new)
-/
@[step]
theorem new_value_spec (value : U16) :
    spqr.encoding.gf.GF16.new value ⦃ (result : spqr.encoding.gf.GF16) =>
      result.value = value ⦄ := by
  simp [spqr.encoding.gf.GF16.new]

end spqr.encoding.gf.GF16
