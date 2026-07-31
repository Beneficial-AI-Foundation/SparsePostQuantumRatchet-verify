/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Chunked.States.Serialize.DecodeChunk
import Spqr.Specs.V1.Chunked.States.Serialize.Message.Serialize
import Spqr.Specs.V1.Chunked.States.Serialize.MessageType.TryFrom
import Spqr.Specs.V1.Chunked.States.Serialize.U8.From

/-! # Spec theorem for
`spqr::v1::chunked::states::serialize::{spqr::v1::chunked::states::Message}::deserialize`

`Message::deserialize` parses the wire encoding produced by `Message::serialize`:

  `[version (1 byte)] ++ [varint(epoch)] ++ [varint(index)] ++ [message_type (1 byte)]`

followed, for the chunk-carrying payload variants, by the chunk block
`[varint(chunk.index)] ++ [chunk_data (32 bytes)]`.  It rejects (with `Error::MsgDecode`)
an empty buffer, a wrong version byte, a zero epoch, an index that does not fit in a `u32`,
a tag byte outside `0..=6`, and any varint/chunk decoding failure.  Trailing bytes after the
consumed prefix are deliberately allowed (forward compatibility), which is why the returned
cursor matters: it marks the end of the message inside the buffer.

We prove that on success the consumed prefix `from[0 .. at)` has exactly the layout above:
byte `0` is the version byte `1`; two well-formed LEB128 blocks follow whose decodings are
the returned `epoch` (nonzero) and `index`; the next byte is the tag of the returned payload
(`payloadTag`, the same model used by `Message.serialize_spec`); and for chunk-carrying
variants a chunk block follows whose index/data are the returned chunk's, with the cursor
landing right after it — all within the buffer.  On failure the error is `Error::MsgDecode`.
This subsumes the source's `hax_lib::ensures`
(`msg.epoch > 0 && at <= from.len()` on the `Ok` path).

The varint blocks are characterized by `varintBlockAt`, which repeats the byte-level
conjuncts of `decode_varint_spec` (terminator byte has its high bit clear, continuation
bytes have it set).  These pin the block length down to a single value for a given buffer,
so a future roundtrip theorem against `Message.serialize_spec`'s `messageBytes` can identify
each block it produced.

**Precondition.** `from.len() + 32 ≤ usize::MAX`, inherited from `decode_chunk_spec` (the
extraction drops the source's `hax_lib::assume!` making `*at += 32` fallible there).

**Axioms.** As for `decode_chunk_spec`, the axiom closure picks up the opaque
`core::fmt::Formatter` type and two `native_decide` instances — extraction artifacts of the
string literals in `decode_chunk`'s `.expect("correct size")` and `MessageType::try_from`'s
out-of-range error message (Aeneas's `toStr` discharges the literal-length side condition
with `by decide +native`) — not proof debt of this theorem.

**Source**: src/v1/chunked/states/serialize.rs (lines 247-278)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states.serialize

-- Shorten the `?`-desugaring (`from_residual`) and `map_err`-closure names used in the proof.
open core.result.Result.Insts Message.deserialize

/-! ## Pure layout predicates -/

/-- `varintBlockAt bytes start n v`: bytes `start, …, start + n - 1` lie inside `bytes` and
form a well-formed LEB128 block decoding (truncated to 64 bits) to `v`: byte `n - 1` is the
terminator (high bit clear) and bytes `0, …, n - 2` are continuation bytes (high bit set).
These are exactly the success conjuncts of `decode_varint_spec`. -/
def varintBlockAt (bytes : List Std.U8) (start n v : ℕ) : Prop :=
  1 ≤ n ∧ n ≤ 10 ∧ start + n ≤ bytes.length ∧
  v = varintVal bytes start n % 2 ^ 64 ∧
  bytes[start + n - 1]!.val < 128 ∧
  ∀ k < n - 1, 128 ≤ bytes[start + k]!.val

/-- `chunkBlockAt bytes start n c`: bytes `start, …, start + n + 31` lie inside `bytes` and
form a chunk block — a LEB128 block of `n` bytes decoding to `c.index` followed by the 32
payload bytes `c.data`.  These are exactly the success conjuncts of `decode_chunk_spec`. -/
def chunkBlockAt (bytes : List Std.U8) (start n : ℕ) (c : encoding.Chunk) : Prop :=
  varintBlockAt bytes start n c.index.val ∧
  start + n + 32 ≤ bytes.length ∧
  c.data.val = bytes.slice (start + n) (start + n + 32)

/-! ## Spec theorem -/

set_option maxHeartbeats 400000 in
-- required because the proof steps through the whole function once per tag branch
-- (eight of them, five containing a `decode_chunk` call)
/-- **Spec theorem for
`spqr::v1::chunked::states::serialize::{spqr::v1::chunked::states::Message}::deserialize`**:

On success (`Ok (msg, index, at1)`), the consumed prefix `from[0 .. at)` is a well-formed
message encoding: the version byte `1`, a varint block decoding to `msg.epoch ≠ 0`, a varint
block decoding to `index`, the tag byte `payloadTag msg.payload`, and — for chunk-carrying
payloads — a chunk block carrying the returned chunk; the cursor `at` lands right after the
consumed bytes, within the buffer (`at ≤ from.len()`, the source's `hax_lib::ensures`).
On failure the error is `Error::MsgDecode`. -/
@[step]
theorem Message.deserialize_spec
    (from1 : alloc.vec.Vec Std.U8)
    (hlen : from1.length + 32 ≤ Std.Usize.max) :
    Message.deserialize from1 ⦃ (p : core.result.Result
        (v1.chunked.states.Message × Std.U32 × Std.Usize) Error) =>
      match p with
      | .Ok (msg, index, at1) =>
        0 < msg.epoch.val ∧ at1.val ≤ from1.length ∧
        -- `0 < from1.length` is implied by `1 + n₁ + n₂ < from1.length` below, but is kept
        -- outside the `∃` so the `[0]!` access next to it is meaningful on its own.
        0 < from1.length ∧ from1.val[0]!.val = 1 ∧
        ∃ n₁ n₂, varintBlockAt from1.val 1 n₁ msg.epoch.val ∧
          varintBlockAt from1.val (1 + n₁) n₂ index.val ∧
          1 + n₁ + n₂ < from1.length ∧
          from1.val[1 + n₁ + n₂]!.val = payloadTag msg.payload ∧
          match msg.payload with
          | .None => at1.val = 2 + n₁ + n₂
          | .Ct1Ack b => b = true ∧ at1.val = 2 + n₁ + n₂
          | .Hdr c | .Ek c | .EkCt1Ack c | .Ct1 c | .Ct2 c =>
            ∃ n₃, chunkBlockAt from1.val (2 + n₁ + n₂) n₃ c ∧
              at1.val = 2 + n₁ + n₂ + n₃ + 32
      | .Err e => e = Error.MsgDecode ⦄ := by
  unfold Message.deserialize
  simp only [core.convert.IntoFrom.into, U8.Insts.CoreConvertFromVersion.from,
    core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
  step*
  -- The `Vec::is_empty` guard: turn `¬isEmpty` into `0 < length`.  `simp_all` is terminal
  -- and bridges the Bool/Prop gap together with `b_post`.
  case hbound => simp_all [List.length_pos_iff]
  match r with
  | .Err e =>
    simp only [CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    exact r_post2.1
  | .Ok epochV =>
    obtain ⟨h1lt, n₁, hat1, hn₁1, hn₁10, hn₁len, hepoch, hterm₁, hcont₁⟩ := r_post2
    step*
    match r1 with
    | .Err e =>
      simp only [CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
      exact r1_post2.1
    | .Ok idx64 =>
      obtain ⟨hatlt, n₂, hat2, hn₂1, hn₂10, hn₂len, hidx64, hterm₂, hcont₂⟩ := r1_post2
      step*
      match r2 with
      | .Err _ =>
        simp only [core.result.Result.map_err_Err,
          closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError,
          closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError.call_once,
          CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
      | .Ok idx =>
        obtain ⟨_, hidx⟩ := r2_post
        simp only [core.result.Result.map_err_Ok, bind_tc_ok]
        step*
        split at r4_post
        -- The eight tag branches fall into three groups closed by multi-tag `case`:
        -- the five chunk-carrying tags (1 Hdr, 2 Ek, 3 EkCt1Ack, 5 Ct1, 6 Ct2) produce
        -- syntactically identical goals — the script below never names the payload
        -- constructor — as do the two chunk-less tags (0 None, 4 Ct1Ack).
        case h_2 | h_3 | h_4 | h_6 | h_7 =>
          -- tags 1, 2, 3, 5, 6: a chunk block follows
          subst r4_post
          simp only [core.result.Result.map_err_Ok, bind_tc_ok]
          step*
          match r6 with
          | .Err e =>
            simp only [CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
            exact r6_post2
          | .Ok c =>
            obtain ⟨n₃, hat4, hn₃1, hn₃10, hat4len, hcidx, hterm₃, hcont₃, hcdata⟩ := r6_post2
            refine ⟨by scalar_tac, hat4len, by omega, ?_, n₁, n₂, ?_, ?_,
              by scalar_tac, ?_, n₃, ?_, by omega⟩
            · rw [getElem!_pos from1.val 0 (by scalar_tac), ← i_post]; scalar_tac
            · exact ⟨hn₁1, hn₁10, hn₁len, hepoch, hterm₁, hcont₁⟩
            · rw [show (1 + n₁ : ℕ) = ↑at1 from hat1.symm]
              exact ⟨hn₂1, hn₂10, hn₂len, by rw [hidx, hidx64], hterm₂, hcont₂⟩
            · simp only [payloadTag]
              rw [show (1 + n₁ + n₂ : ℕ) = ↑at2 by omega,
                getElem!_pos from1.val at2.val (by scalar_tac), ← i3_post]
              assumption
            · rw [show (2 + n₁ + n₂ : ℕ) = ↑at3 by omega]
              exact ⟨⟨hn₃1, hn₃10, by scalar_tac, hcidx, hterm₃, hcont₃⟩, by scalar_tac, hcdata⟩
        case h_1 | h_5 =>
          -- tags 0 (None) and 4 (Ct1Ack): no chunk block, the cursor stops after the tag byte
          subst r4_post
          simp only [core.result.Result.map_err_Ok, bind_tc_ok]
          step*
          refine ⟨by scalar_tac, by scalar_tac, by omega, ?_, n₁, n₂, ?_, ?_,
            by scalar_tac, ?_, by omega⟩
          · rw [getElem!_pos from1.val 0 (by scalar_tac), ← i_post]; scalar_tac
          · exact ⟨hn₁1, hn₁10, hn₁len, hepoch, hterm₁, hcont₁⟩
          · rw [show (1 + n₁ : ℕ) = ↑at1 from hat1.symm]
            exact ⟨hn₂1, hn₂10, hn₂len, by rw [hidx, hidx64], hterm₂, hcont₂⟩
          · simp only [payloadTag]
            rw [show (1 + n₁ + n₂ : ℕ) = ↑at2 by omega,
              getElem!_pos from1.val at2.val (by scalar_tac), ← i3_post]
            assumption
        case h_8 =>
          -- tag > 6: decode error
          subst r4_post
          simp only [core.result.Result.map_err_Err,
            closure_1.Insts.CoreOpsFunctionFnOnceTupleStringError,
            closure_1.Insts.CoreOpsFunctionFnOnceTupleStringError.call_once,
            CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]

end spqr.v1.chunked.states.serialize
