/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Lib.MsgPreamble
public import Spqr.Specs.V1.Chunked.States.Serialize.EncodedBlocks
public import Spqr.Specs.V1.Chunked.States.Serialize.Message.Serialize
public import Spqr.Specs.V1.Chunked.States.Serialize.Message.Deserialize
import Spqr.Auxiliary.Aeneas.SpecImpExists

/-!
# Parsing the bytes of a serialized message gives the message back

`Message::serialize` writes the version byte `1`, `varint(epoch)`, `varint(index)`, the payload
tag and, for the chunk-carrying payloads, `varint(chunk.index) ++ chunk.data`. On receipt,
`msg_preamble` reads the version, epoch and index, and `Message::deserialize` reads the tag and
the chunk from the remaining bytes.

`Message.serialize_parse_roundtrip` composes the three calls: for a message with a nonzero
epoch whose `Ct1Ack` flag, if any, is `true`, the parse returns the version `1`, the epoch, the
index and the message that were serialized. The round trip fails exactly when the epoch is `0`
or the payload is `Ct1Ack(false)`: `msg_preamble` rejects epoch `0`, and `deserialize` always
rebuilds `Ct1Ack(true)`.

The bridges from encoder to decoder are `varintBlockAt_of_map` and `chunkBlockAt_of_map`
(`EncodedBlocks.lean`): bytes laid out as `varintBytes a`, for `a < 2 ^ 64`, form the block
`decode_varint` reads, with value `a`, and bytes laid out as `chunkBytes c` form the block
`decode_chunk` reads, with chunk `c`. The completeness lemmas
`decode_varint_of_block`, `msg_preamble_of_blocks`, `decode_chunk_of_block` and
`Message.deserialize_of_bytes` turn those blocks into successful parses.

**Source**: src/v1/chunked/states/serialize.rs (lines 171-219), src/lib.rs (lines 563-590)
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states.serialize

open core.result.Result.Insts Message.deserialize in
/-- Assume the byte values of `from1` are `payloadTag pl`, then `payloadChunkBytes pl`, then
any bytes, and a `Ct1Ack` payload carries `true`. Then `Message.deserialize e from1` returns
`⟨e, pl⟩`. -/
theorem Message.deserialize_of_bytes (e : Std.U64) (from1 : Slice Std.U8)
    (pl : v1.chunked.states.MessagePayload) (post : List ℕ)
    (hack : ∀ b, pl = .Ct1Ack b → b = true)
    (h : from1.val.map UScalar.val = payloadTag pl :: payloadChunkBytes pl ++ post) :
    Message.deserialize e from1 ⦃ r => r = .Ok ⟨e, pl⟩ ⦄ := by
  have hpos : 0 < from1.length := by
    have := congrArg List.length h; simp at this; scalar_tac
  have h0 : (from1.val[0]!).val = payloadTag pl := by
    rw [getElem!_val_eq_map, h]; simp
  unfold Message.deserialize
  simp only [CoreOpsTry.branch]
  step*
  have hi : i.val = payloadTag pl := by
    rw [i_post, ← h0, getElem!_pos from1.val 0 (by scalar_tac)]
  rcases pl with _ | c | c | c | b | c | c
  all_goals
    simp only [payloadTag] at hi
    rw [hi] at r_post
    subst r_post
    simp only [core.result.Result.map_err_Ok, bind_ok]
  · simp
  all_goals try (obtain rfl := hack _ rfl; simp)
  all_goals
    simp only [payloadTag, payloadChunkBytes] at h
    have hb := chunkBlockAt_of_map_cons from1.val _ post c h
    step with decode_chunk_of_block from1 1#usize _ c (by simpa using hb) as ⟨r2, at2, hr2, _⟩
    subst hr2
    simp

/-- Parsing the bytes that `Message::serialize` writes gives the message back.
Take a message with a nonzero epoch whose `Ct1Ack` flag, if it has one, is `true`, and any
index. Then `Message::serialize` succeeds. `msg_preamble` parses its output to a preamble with
version `1` and the message's epoch and index. `Message::deserialize` on that epoch and the
remaining bytes returns the message. -/
theorem Message.serialize_parse_roundtrip
    (m : v1.chunked.states.Message) (i : Std.U32)
    (hepoch : 0 < m.epoch.val)
    (hack : ∀ b, m.payload = .Ct1Ack b → b = true) :
    ∃ (bytes : alloc.vec.Vec Std.U8) (p : MsgPreamble),
      Message.serialize m i = ok bytes ∧
      msg_preamble bytes = ok (.Ok p) ∧
      p.version = 1#u8 ∧ p.epoch = m.epoch ∧ p.index = i ∧
      Message.deserialize p.epoch p.remaining = ok (.Ok m) := by
  obtain ⟨bytes, hser, hbytes⟩ := WP.spec_imp_exists (Message.serialize_spec m i)
  simp only [messageBytes] at hbytes
  set body := payloadTag m.payload :: payloadChunkBytes m.payload with hbody
  have he : m.epoch.val < 2 ^ 64 := by scalar_tac
  have hi : i.val < 2 ^ 32 := by scalar_tac
  -- The two preamble varints, read off the serializer's layout.
  have h₁ := varintBlockAt_of_map bytes.val [1] (varintBytes i.val ++ body) m.epoch.val he
    (by rw [hbytes]; simp)
  have h₂ := varintBlockAt_of_map bytes.val (1 :: varintBytes m.epoch.val) body i.val
    (by scalar_tac) (by rw [hbytes]; simp)
  simp only [List.length_nil, List.length_cons] at h₁ h₂
  have hne : 0 < bytes.length := by
    have := congrArg List.length hbytes; simp at this; simp [alloc.vec.Vec.length]; omega
  obtain ⟨r, hr, p, rfl, hpv, hpe, hpi, hpr⟩ := WP.spec_imp_exists
    (msg_preamble_of_blocks bytes _ _ m.epoch.val i.val hne h₁ (by omega)
      (by rwa [Nat.add_comm] at h₂) hi)
  have hrem : p.remaining.val.map UScalar.val = body ++ [] := by
    rw [hpr, List.map_drop, hbytes, List.append_nil,
      show 1 + (varintBytes m.epoch.val).length + (varintBytes i.val).length =
        ((varintBytes m.epoch.val).length + (varintBytes i.val).length) + 1 by omega,
      List.drop_succ_cons, List.drop_left' (by simp)]
  obtain ⟨d, hd, rfl⟩ := WP.spec_imp_exists
    (Message.deserialize_of_bytes p.epoch p.remaining m.payload [] hack hrem)
  refine ⟨bytes, p, hser, hr, ?_, UScalar.eq_of_val_eq hpe, UScalar.eq_of_val_eq hpi, ?_⟩
  · apply UScalar.eq_of_val_eq
    rw [hpv, getElem!_val_eq_map, hbytes]; simp
  · rw [hd, show p.epoch = m.epoch from UScalar.eq_of_val_eq hpe]

end spqr.v1.chunked.states.serialize
