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

`Message::deserialize` parses the body of a chunked message, i.e. what follows the common
preamble `[version] ++ [varint(epoch)] ++ [varint(index)]` (parsed separately by
`spqr::msg_preamble`, see `Spqr/Specs/Lib/MsgPreamble.lean`; the epoch is passed in):

  `[tag byte]`

plus, for the chunk-carrying tags, a chunk block `[varint(chunk.index)] ++ [32 data bytes]`.
Trailing bytes past the consumed prefix are allowed (forward compatibility).

We prove that on success the returned message carries the given `epoch`, `from[0]` is the tag
byte `payloadTag msg.payload` (the model `Message.serialize_spec` also uses), and for the
chunk-carrying payloads a chunk block carrying the returned chunk starts at offset `1`, within
the buffer.  Every failure is `Error::MsgDecode`.

The chunk block is stated via `chunkBlockAt`, so the layout claimed here is literally what
`decode_chunk_spec` establishes.

**Source**: src/v1/chunked/states/serialize.rs (lines 200-219)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states.serialize

-- Shorten the `?`-desugaring (`from_residual`) and `map_err`-closure names used in the proof.
open core.result.Result.Insts Message.deserialize

/-- Discharge a `?`-propagated error branch. -/
local macro "close_err" : tactic =>
  `(tactic| simp_all only [core.result.Result.map_err_Ok, core.result.Result.map_err_Err,
    closure.Insts.CoreOpsFunctionFnOnceTupleStringError,
    closure.Insts.CoreOpsFunctionFnOnceTupleStringError.call_once,
    CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok])

/-- **Spec theorem for
`spqr::v1::chunked::states::serialize::{spqr::v1::chunked::states::Message}::deserialize`**:

On success (`Ok msg`) the message carries the given `epoch`, the buffer is non-empty, its first
byte is the tag byte `payloadTag msg.payload`, and for the chunk-carrying payloads a chunk block
carrying the returned chunk starts right after the tag byte (`chunkBlockAt from 1 n₃ c`, which
includes `1 + n₃ + 32 ≤ from.len()`); a `Ct1Ack` payload carries `true`.  On failure the error
is `Error::MsgDecode`. -/
@[step]
theorem Message.deserialize_spec
    (epoch : Std.U64) (from1 : Slice Std.U8)
    (hlen : from1.length + 32 ≤ Std.Usize.max) :
    Message.deserialize epoch from1 ⦃ (p : core.result.Result v1.chunked.states.Message Error) =>
      match p with
      | .Ok msg =>
        msg.epoch = epoch ∧
        0 < from1.length ∧ from1.val[0]!.val = payloadTag msg.payload ∧
          match msg.payload with
          | .None => True
          | .Ct1Ack b => b = true
          | .Hdr c | .Ek c | .EkCt1Ack c | .Ct1 c | .Ct2 c =>
            ∃ n₃, chunkBlockAt from1.val 1 n₃ c
      | .Err e => e = Error.MsgDecode ⦄ := by
  unfold Message.deserialize
  simp only [core.result.Result.Insts.CoreOpsTry.branch]
  step*
  -- The `is_empty` guard: turn `¬isEmpty` into `0 < length`.
  have hpos : 0 < from1.length := by
    have : ¬from1.length = 0 := by rw [← ‹(b = true) = (from1.length = 0)›]; assumption
    omega
  have h0 : (from1.val[0]!).val = i.val := by
    rw [getElem!_pos from1.val 0 (by scalar_tac), ‹i = _›]
  split at *
  case h_2 | h_3 | h_4 | h_6 | h_7 =>
    -- tags 1, 2, 3, 5, 6: a chunk block follows
    subst ‹r = _›
    simp only [core.result.Result.map_err_Ok, bind_ok]
    step as ⟨r2, _, _, hr2⟩
    rcases r2 with c | e
    · obtain ⟨n₃, -, hblk⟩ := hr2
      simp only [bind_ok, WP.spec_ok]
      refine ⟨trivial, hpos, ?_, n₃, hblk⟩
      rw [h0]; simp only [payloadTag]; scalar_tac
    · close_err
  case h_1 | h_5 =>
    subst ‹r = _›
    simp only [core.result.Result.map_err_Ok, bind_ok, WP.spec_ok]
    simp only [h0, payloadTag, hpos, true_and, and_true]; scalar_tac
  case h_8 =>
    -- tag > 6: `MessageType::try_from` fails and `map_err` turns it into `MsgDecode`
    obtain ⟨_, rfl⟩ : ∃ e, r = .Err e := ‹_›
    close_err

end spqr.v1.chunked.states.serialize
