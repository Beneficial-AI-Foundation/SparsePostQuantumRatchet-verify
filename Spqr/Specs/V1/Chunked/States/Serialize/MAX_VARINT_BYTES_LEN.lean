/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs

/-! # Spec theorem for `spqr::v1::chunked::states::serialize::MAX_VARINT_BYTES_LEN`

`MAX_VARINT_BYTES_LEN` is the maximum number of bytes a LEB128-style varint encoding of a `u64`
can occupy: each byte carries 7 payload bits, so a 64-bit value needs at most `⌈64 / 7⌉ = 10`
bytes. `encode_varint` and `decode_varint` use it to bound their loops.

This constant records that bound: `MAX_VARINT_BYTES_LEN = 10#usize`

**Source**: src/v1/chunked/states/serialize.rs -/

namespace spqr.v1.chunked.states.serialize

/-- **Spec theorem for `v1.chunked.states.serialize.MAX_VARINT_BYTES_LEN`**:

Concretely: `MAX_VARINT_BYTES_LEN.val = 10` -/
@[simp]
theorem MAX_VARINT_BYTES_LEN_val :
    MAX_VARINT_BYTES_LEN.val = 10 := by
  simp [MAX_VARINT_BYTES_LEN]

end spqr.v1.chunked.states.serialize
