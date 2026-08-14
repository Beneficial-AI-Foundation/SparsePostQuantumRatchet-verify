/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::chain::{spqr::chain::KeyHistory}::KEY_SIZE`

`KEY_SIZE` is an associated constant of `KeyHistory` that gives the byte size of a single stored
key record in the `data` vector.  Each record consists of a 4-byte big-endian `u32` index
concatenated with a 32-byte key, for a total of **36 bytes**.

  • Value: **36** (computed as `4 + 32`).

The constant is used throughout `KeyHistory` to stride over the flat `Vec<u8>` backing store:
`get_loop` scans in steps of `KEY_SIZE`, `add` extends the vector by exactly `KEY_SIZE` bytes,
and `remove` shifts data in `KEY_SIZE`-sized chunks.

**Source**: spqr/src/chain.rs (line 130:4-130:35)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.KeyHistory

/--
**Spec theorem for `spqr.chain.KeyHistory.KEY_SIZE`**:

The constant satisfies:

  `KEY_SIZE = ok 36#usize`

This is the exact value used in the Rust source:

```rust
const KEY_SIZE: usize = 4 + 32;
```

The extracted Lean definition computes `4#usize + 32#usize` inside the `Result` monad.  The
theorem states that this computation succeeds (does not overflow) and produces `36#usize`.

**Source**: spqr/src/chain.rs (line 130:4-130:35)
-/

@[step]
theorem KEY_SIZE_spec :
    KEY_SIZE ⦃ fun res => res = 36#usize ⦄ := by
  unfold KEY_SIZE
  step
  scalar_tac

end spqr.chain.KeyHistory
