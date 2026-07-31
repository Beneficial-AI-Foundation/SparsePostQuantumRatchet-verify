/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Chunked.States.Serialize.EncodeChunk
import Spqr.Specs.V1.Chunked.States.Serialize.EncodeVarint
import Spqr.Specs.V1.Chunked.States.Serialize.MessageType.FromPayload
import Spqr.Specs.V1.Chunked.States.Serialize.U8.From

/-! # Spec theorem for
`spqr::v1::chunked::states::serialize::{spqr::v1::chunked::states::Message}::serialize`

`Message::serialize` produces the wire encoding of a `Message` for a given ratchet `index`:

  `[version (1 byte)] ++ [varint(epoch)] ++ [varint(index)] ++ [message_type (1 byte)]`

followed, for the chunk-carrying payload variants (`Hdr`, `Ek`, `EkCt1Ack`, `Ct1`, `Ct2`),
by the chunk block `[varint(chunk.index)] ++ [chunk_data (32 bytes)]` — the same block
`encode_chunk` emits.  The `None` and `Ct1Ack` variants carry no chunk.

We prove functional correctness: the resulting bytes are exactly
`messageBytes self index.val`, the pure model of the layout above.  The theorem needs no
precondition: serialization starts from an empty buffer, so the intermediate lengths are
bounded by `1 + 10 + 10 + 1 = 22` and every overflow guard (the pushes, the varints, and
`encode_chunk`'s `+ 42` entry bound) is discharged numerically.  This subsumes the
`hax_lib::ensures` of the source (`res.len() > 0 && res[0] == Version::V1.into()`): the model
starts with the literal version byte `1`.

**Source**: src/v1/chunked/states/serialize.rs (lines 221-245)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states.serialize

/-! ## Pure model -/

/-- The message-type tag byte of a payload: the discriminant of the like-named
`MessageType` variant (see `MessageType.from_payload` and the `u8` conversion). -/
def payloadTag (p : v1.chunked.states.MessagePayload) : ℕ :=
  match p with
  | .None => 0
  | .Hdr _ => 1
  | .Ek _ => 2
  | .EkCt1Ack _ => 3
  | .Ct1Ack _ => 4
  | .Ct1 _ => 5
  | .Ct2 _ => 6

/-- The chunk block of a payload: `varintBytes (chunk.index) ++ chunk.data` for the
chunk-carrying variants, empty for `None` and `Ct1Ack`. -/
def payloadChunkBytes (p : v1.chunked.states.MessagePayload) : List ℕ :=
  match p with
  | .None | .Ct1Ack _ => []
  | .Hdr c | .Ek c | .EkCt1Ack c | .Ct1 c | .Ct2 c =>
      varintBytes c.index.val ++ c.data.val.map UScalar.val

/-- Pure model of `Message::serialize`: version byte `1`, LEB128 epoch, LEB128 index,
message-type tag, then the payload's chunk block (if any). -/
def messageBytes (msg : v1.chunked.states.Message) (index : ℕ) : List ℕ :=
  1 :: (varintBytes msg.epoch.val ++ varintBytes index ++
    payloadTag msg.payload :: payloadChunkBytes msg.payload)

/-! ## Spec theorem -/

/-- **Spec theorem for
`spqr::v1::chunked::states::serialize::{spqr::v1::chunked::states::Message}::serialize`**:

`Message::serialize` always succeeds (no precondition: the buffer starts empty, so no
overflow guard can fire) and the output bytes are exactly `messageBytes self index.val` —
in particular the output is nonempty and starts with the version byte `1`, which is the
source's `hax_lib::ensures`. -/
@[step]
theorem Message.serialize_spec (self : v1.chunked.states.Message) (index : Std.U32) :
    Message.serialize self index ⦃ (out : alloc.vec.Vec Std.U8) =>
      out.val.map UScalar.val = messageBytes self index.val ⦄ := by
  unfold Message.serialize
  simp only [core.convert.IntoFrom.into, U8.Insts.CoreConvertFromVersion.from,
    alloc.vec.Vec.with_capacity, bind_tc_ok]
  step*
  all_goals
    simp_all [messageBytes, payloadTag, payloadChunkBytes, List.map_append]
  all_goals scalar_tac

end spqr.v1.chunked.states.serialize
