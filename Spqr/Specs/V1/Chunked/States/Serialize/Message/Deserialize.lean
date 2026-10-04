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

`Message::deserialize` parses the encoding produced by `Message::serialize`:

  `[version = 1] ++ [varint(epoch)] ++ [varint(index)] ++ [tag byte]`

plus, for the chunk-carrying tags, a chunk block `[varint(chunk.index)] ++ [32 data bytes]`.
Trailing bytes past the consumed prefix are allowed (forward compatibility), so the returned
cursor is what marks the end of the message.

We prove that on success `from[0 .. at)` has exactly that layout, with the two varint blocks
decoding to the returned `epoch` (nonzero) and `index`, the tag byte equal to
`payloadTag msg.payload` (the model `Message.serialize_spec` also uses), and the cursor landing
right after the last block, within the buffer.  Every failure is `Error::MsgDecode`.

The blocks are stated via `varintBlockAt` and `chunkBlockAt`, so the layout claimed here is
literally what `decode_varint_spec` and `decode_chunk_spec` establish.

**Source**: src/v1/chunked/states/serialize.rs (lines 247-278)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states.serialize

-- Shorten the `?`-desugaring (`from_residual`) and `map_err`-closure names used in the proof.
open core.result.Result.Insts Message.deserialize

/-- Discharge a `?`-propagated error branch. -/
local macro "close_err" : tactic =>
  `(tactic| simp_all only [core.result.Result.map_err_Ok, core.result.Result.map_err_Err,
    closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError,
    closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError.call_once,
    closure_1.Insts.CoreOpsFunctionFnOnceTupleStringError,
    closure_1.Insts.CoreOpsFunctionFnOnceTupleStringError.call_once,
    CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from, bind_tc_ok, WP.spec_ok])

/-- **Spec theorem for
`spqr::v1::chunked::states::serialize::{spqr::v1::chunked::states::Message}::deserialize`**:

On success (`Ok (msg, index, at)`) the prefix `from[0 .. at)` is the layout above — version
byte `1`, a varint block decoding to `msg.epoch ≠ 0`, a varint block decoding to `index`, the
tag byte `payloadTag msg.payload`, then a chunk block carrying the returned chunk for the
chunk-carrying payloads — and `at ≤ from.len()`.  On failure the error is `Error::MsgDecode`. -/
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
  | .Err _ => close_err
  | .Ok epochV =>
    obtain ⟨-, n₁, hat₁, hblk₁⟩ :
        1 < from1.length ∧ ∃ n, _ = 1 + n ∧ varintBlockAt (↑from1) 1 n ↑epochV := by
      assumption
    step*
    match r1 with
    | .Err _ => close_err
    | .Ok idx64 =>
      obtain ⟨-, n₂, hat₂, hblk₂⟩ :
          _ < from1.length ∧ ∃ n, _ = _ + n ∧ varintBlockAt (↑from1) _ n ↑idx64 := by
        assumption
      step*
      match r2 with
      | .Err _ => close_err
      | .Ok idx =>
        obtain ⟨-, hidx⟩ : _ ∧ idx.val = idx64.val := by assumption
        simp only [core.result.Result.map_err_Ok, bind_tc_ok]
        step*
        rw [hat₁, ← hidx] at hblk₂
        have h0 : (from1.val[0]!).val = 1 := by
          rw [getElem!_pos from1.val 0 (by scalar_tac), ← i_post]; scalar_tac
        have hbyte : (from1.val[1 + n₁ + n₂]!).val = i3.val := by
          rw [show (1 + n₁ + n₂ : ℕ) = at1.val by omega,
            getElem!_pos from1.val at1.val (by scalar_tac), ← i3_post]
        split at r4_post
        case h_2 | h_3 | h_4 | h_6 | h_7 =>
          -- tags 1, 2, 3, 5, 6: a chunk block follows
          subst r4_post
          simp only [core.result.Result.map_err_Ok, bind_tc_ok]
          step*
          match r6 with
          | .Err _ => close_err
          | .Ok c =>
            obtain ⟨n₃, hat₃, hcblk, hclen, hcdata⟩ :
                ∃ n, _ = _ + n + 32 ∧ chunkBlockAt (↑from1) _ n c := by assumption
            have hat2v : at2.val = 2 + n₁ + n₂ := by omega
            rw [hat2v] at hcblk hclen hcdata
            refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, h0, n₁, n₂, hblk₁, hblk₂,
              by scalar_tac, ?_, n₃, ⟨hcblk, hclen, hcdata⟩, by scalar_tac⟩
            simp only [payloadTag]; rw [hbyte]; omega
        case h_1 | h_5 =>
          subst r4_post
          simp only [core.result.Result.map_err_Ok, bind_tc_ok]
          step*
          refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, h0, n₁, n₂, hblk₁, hblk₂,
            by scalar_tac, ?_, ?_⟩
          · simp only [payloadTag]; rw [hbyte]; omega
          · scalar_tac
        case h_8 =>
          -- tag > 6: `MessageType::try_from` fails and `map_err` turns it into `MsgDecode`
          subst r4_post
          close_err

end spqr.v1.chunked.states.serialize
