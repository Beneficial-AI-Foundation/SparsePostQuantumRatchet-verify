/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Chunked.States.Serialize.DecodeVarint

/-! # Spec theorem for `spqr::v1::chunked::states::serialize::decode_chunk`

`decode_chunk` reads a `Chunk` from the byte buffer `from` at cursor `at`, advancing the cursor
past the bytes it consumed.  A chunk is serialized as

  `[varint(index)] ++ [data (32 bytes)]`

so decoding is `decode_varint` followed by a verbatim 32-byte read; the chunk index is rejected
if it does not fit in a `u16`.

We prove functional correctness: on success the index is the LEB128 decoding (`varintVal`) of
the `n` bytes consumed by `decode_varint`, the payload is exactly the next 32 bytes of the
buffer, and the cursor ends at `at + n + 32`, still within the buffer.  Two points deserve
mention.

* **Precondition.** The extraction drops the source's `hax_lib::assume!(*at < usize::MAX - 32)`,
  so `*at += 32` is a fallible addition.  We discharge it from `from.len() + 32 ≤ usize::MAX`,
  which is weaker than a bound on the entry cursor: `decode_varint` already guarantees
  `at ≤ from.len()` on the path where the addition happens.
* **Cursor on failure.** The source mutates `*at` *before* the bounds check, so on the two
  error paths of `decode_chunk` itself the cursor has already advanced by `n + 32` — unlike
  `decode_varint`, which leaves it untouched on failure.  Hence the postcondition only claims
  monotonicity `at ≤ *future(at)`, not `*future(at) = at`, in the error case.  This is what the
  caller `Message::deserialize` relies on: its `ensures` constrains the cursor on success only.

Unlike the other specs in this directory, the axiom closure of `decode_chunk_spec` contains two
extra axioms, both coming from the extracted `.expect("correct size")` in the function body and
not from the proof: Aeneas models `core::fmt::Formatter` as an opaque type (`axiom`), and its
`toStr` discharges the string-literal length side condition with `by decide +native`, whose
`native_decide` axiom is shared through the first extraction site,
`chain.ChainEpochDirection.next_key_internal._proof_6`.

**Source**: src/v1/chunked/states/serialize.rs (lines 190-202)
-/

open Aeneas Aeneas.Std Result Error

-- Use the no-overflow cast spec so `step` learns `(cast .U16 val).val = val.val` directly,
-- avoiding bit-vector reasoning about the `index as u16` conversion.
attribute [local step] UScalar.cast_inBounds_spec

namespace spqr.v1.chunked.states.serialize

/-- **Spec theorem for `spqr::v1::chunked::states::serialize::decode_chunk`**:

The cursor never moves backwards and, on success, `decode_chunk` consumed a varint of `n` bytes
(`1 ≤ n ≤ 10`) followed by the 32-byte payload, all within the buffer: the cursor ends at
`at + n + 32 ≤ from.len()`, the chunk index is the LEB128 decoding of the varint bytes — so
the decoded value fits in a `u16`, since `c.index` does — and the chunk payload is exactly
`from[at + n .. at + n + 32]`.  On failure the error is `MsgDecode`.

The two byte-level conjuncts — byte `n-1` is the terminator (high bit clear) and bytes
`0, …, n-2` are continuation bytes (high bit set) — are inherited verbatim from
`decode_varint_spec`.  They are what pins `n` down to a single value for a given buffer, so a
future roundtrip theorem against `encode_chunk` can identify the varint block it produced. -/
@[step]
theorem decode_chunk_spec
    (from1 : alloc.vec.Vec Std.U8) (at1 : Std.Usize)
    (hlen : from1.length + 32 ≤ Std.Usize.max) :
    decode_chunk from1 at1 ⦃ (p : (core.result.Result encoding.Chunk Error) × Std.Usize) =>
      at1.val ≤ p.2.val ∧
      (match p.1 with
       | .Ok c =>
          ∃ n, p.2.val = at1.val + n + 32 ∧ 1 ≤ n ∧ n ≤ 10 ∧
            p.2.val ≤ from1.length ∧
            c.index.val = varintVal from1.val at1.val n % 2 ^ 64 ∧
            from1.val[at1.val + n - 1]!.val < 128 ∧
            (∀ k < n - 1, 128 ≤ from1.val[at1.val + k]!.val) ∧
            c.data.val = from1.val.slice (at1.val + n) (at1.val + n + 32)
       | .Err e => e = Error.MsgDecode) ⦄ := by
  unfold decode_chunk
  step
  match r with
  | .Err e =>
    -- `?` propagates the error and returns the cursor as `decode_varint` left it.
    step*
  | .Ok v =>
    obtain ⟨_hin, n, hat2, hn1, hn10, hnlen, hval, hterm, hcont⟩ := r_post2
    -- Reduce `?` on the `Ok` eagerly: this feeds the decoded value into the continuation
    -- directly, instead of leaving it behind a `ControlFlow` equation on a fresh variable.
    simp only [core.result.Result.Insts.CoreOpsTry.branch]
    -- `step*` runs the cursor advance, both bounds checks (closing the two error paths), the
    -- `u16` cast and the 32-byte subslice; the overflow guard follows from `hlen` and `hnlen`.
    step*
    match r1 with
    | .Err () =>
      -- The subslice spans `[at2, at2 + 32)`, so `try_into` cannot have failed.
      exact absurd (by scalar_tac : s.length = 32) r1_post
    | .Ok a =>
      obtain ⟨ha, _halen⟩ := r1_post
      refine ⟨by scalar_tac, n, by scalar_tac, hn1, hn10, by scalar_tac, by rw [i1_post, hval],
        hterm, hcont, ?_⟩
      rw [ha, s_post1, at3_post, hat2]

end spqr.v1.chunked.states.serialize
