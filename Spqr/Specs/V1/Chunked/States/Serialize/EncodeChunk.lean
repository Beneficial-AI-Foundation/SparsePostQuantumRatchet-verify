/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs
import Spqr.Specs.Aeneas.IndexRangeFull
import Spqr.Specs.Aeneas.VecExtendFromSlice
import Spqr.Specs.V1.Chunked.States.Serialize.EncodeVarint

/-! # Spec theorem for `spqr::v1::chunked::states::serialize::encode_chunk`

`encode_chunk` appends the wire encoding of a `Chunk` to the byte buffer `into`.  A chunk is
a 16-bit index together with a fixed 32-byte payload, and it is serialized as

  `[varint(index)] ++ [data (32 bytes)]`

i.e. the LEB128 encoding of the index (1–3 bytes for a `u16`, see `varintBytes`) followed
verbatim by the payload bytes.

We prove functional correctness: the result is exactly `into` extended by those two blocks,
with nothing dropped or reordered.  The precondition `into.len() + 42 ≤ usize::MAX` covers both
the pushes of `encode_varint` (at most 10 bytes) and the 32-byte `extend_from_slice`.  It is
stated on the *entry* buffer, so it is strictly stronger than — and implies — the mid-function
`hax_lib::assume!(into.len() < usize::MAX - 32)` of the Rust source, which constrains the buffer
only after the varint has been pushed.  Since the varint of a `u16` is at most 3 bytes, `+ 35`
would in fact suffice; `+ 42` is what lets `step*` discharge the `extend_from_slice` overflow
guard from `encode_varint_spec`'s generic 10-byte bound alone.

**Source**: src/v1/chunked/states/serialize.rs (lines 184-188)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states.serialize

/-- **Spec theorem for `spqr::v1::chunked::states::serialize::encode_chunk`**:

Under the no-overflow precondition `into.len() + 42 ≤ usize::MAX`, `encode_chunk c into`
succeeds and returns `into ++ tail ++ c.data`, where `tail` (read as natural-number byte
values) is exactly `varintBytes c.index`, the LEB128 encoding of the chunk index — between
1 and 3 bytes, since the index is a `u16`.  The 32-byte payload is appended unchanged. -/
@[step]
theorem encode_chunk_spec
    (c : encoding.Chunk) (into : alloc.vec.Vec Std.U8)
    (hlen : into.length + 42 ≤ Std.Usize.max) :
    encode_chunk c into ⦃ (out : alloc.vec.Vec Std.U8) =>
      ∃ tail, out.val = into.val ++ tail ++ c.data.val ∧
        tail.map UScalar.val = varintBytes c.index.val ∧
        1 ≤ tail.length ∧ tail.length ≤ 3 ⦄ := by
  unfold encode_chunk
  -- `step*` runs the two calls: `encode_varint` (giving the varint block `into1`) and
  -- `extend_from_slice` (appending the payload); both overflow guards follow from `hlen`.
  step*
  -- `i` is the `u16` index widened to `u64`, so it has the same value.
  have hi : i.val = c.index.val := by scalar_tac
  have h_tail3 : into1.length ≤ 3 := by
    have h3 := varintBytes_length_le_three (a := i.val) (by scalar_tac)
    have hlen_eq := congrArg List.length into1_post2
    simp only [List.length_map] at hlen_eq
    omega
  refine ⟨into1, ?_, by rw [into1_post2, hi], into1_post3, h_tail3⟩
  rw [out_post, into1_post1]
  simp only [Array.val_to_slice, List.append_assoc]

end spqr.v1.chunked.states.serialize
