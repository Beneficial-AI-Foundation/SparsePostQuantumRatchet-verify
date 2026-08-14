/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::chain::DEFAULT_CHAIN_PARAMS`

`DEFAULT_CHAIN_PARAMS` is a compile-time constant that provides the library's built-in default
values for `ChainParams`, the two tunable parameters governing ratchet chain behaviour:

  • `max_jump`    — the maximum forward-jump distance (epoch gap) the receiver will tolerate
                    before rejecting a message.  Default: **25 000**.
  • `max_ooo_keys` — the maximum number of out-of-order message keys the receiver retains
                      for delayed / reordered messages.  Default: **2 000**.

These defaults are substituted whenever a protobuf `ChainParamsPB` carries a zero value for
either field (the protobuf zero-default convention), and are also returned by the `Default`
trait implementation for `ChainParams`.

**Source**: spqr/src/chain.rs (lines 34:0-37:2)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain

/--
**Spec theorem for `spqr.chain.DEFAULT_CHAIN_PARAMS`**:

The library-wide default `ChainParams` constant satisfies:

  • `DEFAULT_CHAIN_PARAMS.max_jump    = 25000#u32`
  • `DEFAULT_CHAIN_PARAMS.max_ooo_keys = 2000#u32`

These are the exact values used in the Rust source:

```rust
const DEFAULT_CHAIN_PARAMS: ChainParams = ChainParams {
    max_jump: 25_000,
    max_ooo_keys: 2_000,
};
```

The theorem states that `DEFAULT_CHAIN_PARAMS` is definitionally equal to the struct literal
`{ max_jump := 25000#u32, max_ooo_keys := 2000#u32 }`.

**Source**: spqr/src/chain.rs (lines 34:0-37:2)
-/
@[simp]
theorem DEFAULT_CHAIN_PARAMS_spec :
    chain.DEFAULT_CHAIN_PARAMS.max_jump = 25000#u32 ∧
    chain.DEFAULT_CHAIN_PARAMS.max_ooo_keys = 2000#u32  := by
  unfold chain.DEFAULT_CHAIN_PARAMS
  grind

end spqr.chain
