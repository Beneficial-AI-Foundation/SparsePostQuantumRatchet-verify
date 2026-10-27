/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Lib.MsgPreamble
public import Spqr.Specs.Lib.Recv.ParseEq
public import Spqr.Specs.V1.Chunked.States.Serialize.Message.Deserialize
import Spqr.Auxiliary.Aeneas.SpecImpExists

/-!
# Messages and their byte encodings are not one-to-one

A message goes from one party to the other as a byte string. `Message::serialize` writes the
bytes. The receiver reads them back in two stages: `msg_preamble` reads the version, epoch and
index, and `Message::deserialize` reads the message from the remaining bytes. This file shows
that neither direction is injective (one-to-one): two messages can have the same bytes, and
several byte strings can parse to the same message.

The round trip gives a message back only if its epoch is nonzero and its `Ct1Ack` flag, if
any, is `true`: `msg_preamble` rejects epoch `0`, and the first witness below rules out
`Ct1Ack false`. The witnesses:

* For a `Ct1Ack` payload, `serialize` writes only the type tag, and
  `MessageType::from_payload` sends both Booleans to one tag, so two distinct messages have one
  encoding. `States::send` builds only `Ct1Ack true`, so this limits the domain of the round
  trip. It is not a collision between two messages that are sent.
* `decode_varint` accepts a non-minimal LEB128 block, so `01 01 00 00` and `01 81 00 00 00`
  have one whole preamble and hence one message.
* `Message::deserialize` ignores bytes after the message, so appending a byte changes only the
  preamble's `remaining`.

`recv_on_witnesses_eq` adds that `recv` cannot tell the colliding byte strings apart: by
`recv_eq_of_parse_eq` it returns the same result on them from any state.

**Source**: src/v1/chunked/states/serialize.rs (lines 93-153, 171-219), src/lib.rs (lines
507-590)
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states.serialize

/-- `serialize` writes the same bytes for `Ct1Ack false` and `Ct1Ack true`: it writes only the
type tag, and both Booleans map to the tag of `MessageType::Ct1Ack`. -/
theorem Message.serialize_ct1Ack_eq (i : Std.U32) (e : Std.U64) :
    Message.serialize ⟨e, .Ct1Ack false⟩ i = Message.serialize ⟨e, .Ct1Ack true⟩ i := by
  simp only [Message.serialize, MessageType.from_payload]

/-- A body with tag byte `0` deserializes to `{ epoch, payload := None }`. -/
private theorem deserialize_eq_none (e : Std.U64) (s : Slice Std.U8) (hpos : 0 < s.length)
    (h0 : s.val[0]! = 0#u8) : Message.deserialize e s = ok (.Ok ⟨e, .None⟩) := by
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists (Message.deserialize_none e s hpos h0)
  exact hr

end spqr.v1.chunked.states.serialize

namespace spqr

/-- A preamble is determined by its version, the values of its epoch and index, and the bytes
of `remaining`. -/
private theorem msgPreamble_eq {q p : MsgPreamble} (h₁ : q.version = p.version)
    (h₂ : q.epoch.val = p.epoch.val) (h₃ : q.index.val = p.index.val)
    (h₄ : q.remaining.val = p.remaining.val) : q = p := by
  obtain ⟨qv, qe, qi, qr⟩ := q
  obtain ⟨pv, pe, pi, pr⟩ := p
  simp only at h₁ h₂ h₃ h₄
  simp only [MsgPreamble.mk.injEq]
  exact ⟨h₁, UScalar.eq_of_val_eq h₂, UScalar.eq_of_val_eq h₃, Slice.ext _ _ h₄⟩

/-- A message whose varint blocks are given and whose preamble fields match `p` parses to `p`. -/
private theorem msg_preamble_eq_of_blocks (b : alloc.vec.Vec Std.U8) (p : MsgPreamble)
    (n₁ n₂ : ℕ) (hne : 0 < b.length)
    (h₁ : varintBlockAt b.val 1 n₁ p.epoch.val) (he : p.epoch.val ≠ 0)
    (h₂ : varintBlockAt b.val (1 + n₁) n₂ p.index.val)
    (hv : b.val[0]! = p.version) (hr : b.val.drop (1 + n₁ + n₂) = p.remaining.val) :
    msg_preamble b = ok (.Ok p) := by
  obtain ⟨r, hr', q, rfl, hqv, hqe, hqi, hqr⟩ := WP.spec_imp_exists
    (msg_preamble_of_blocks b n₁ n₂ p.epoch.val p.index.val hne h₁ he h₂ (by scalar_tac))
  rw [hr', msgPreamble_eq (hqv.trans hv) hqe hqi (hqr.trans hr)]

/-- The minimal encoding `01 01 00 00` parses to version `1`, epoch `1`, index `0` and
`remaining = [00]`. -/
theorem msg_preamble_minimal_witness (b : alloc.vec.Vec Std.U8)
    (hb : b.val = [1#u8, 1#u8, 0#u8, 0#u8]) (p : MsgPreamble)
    (hp : p.version = 1#u8 ∧ p.epoch = 1#u64 ∧ p.index = 0#u32 ∧ p.remaining.val = [0#u8]) :
    msg_preamble b = ok (.Ok p) := by
  obtain ⟨hpv, hpe, hpi, hpr⟩ := hp
  apply msg_preamble_eq_of_blocks b p 1 1 <;>
    simp [alloc.vec.Vec.length, hb, hpv, hpe, hpi, hpr, varintBlockAt, varintVal]

/-- The encoding `01 81 00 00 00`, whose epoch block `81 00` is not minimal, parses to the same
preamble as `01 01 00 00`. -/
theorem msg_preamble_nonminimal_witness (b : alloc.vec.Vec Std.U8)
    (hb : b.val = [1#u8, 129#u8, 0#u8, 0#u8, 0#u8]) (p : MsgPreamble)
    (hp : p.version = 1#u8 ∧ p.epoch = 1#u64 ∧ p.index = 0#u32 ∧ p.remaining.val = [0#u8]) :
    msg_preamble b = ok (.Ok p) := by
  obtain ⟨hpv, hpe, hpi, hpr⟩ := hp
  apply msg_preamble_eq_of_blocks b p 2 1 <;>
    simp [alloc.vec.Vec.length, hb, hpv, hpe, hpi, hpr, varintBlockAt, varintVal]

/-- The encoding `01 01 00 00 00`, with one trailing byte, parses to version `1`, epoch `1`,
index `0` and `remaining = [00, 00]`. -/
theorem msg_preamble_trailing_witness (b : alloc.vec.Vec Std.U8)
    (hb : b.val = [1#u8, 1#u8, 0#u8, 0#u8, 0#u8]) (p : MsgPreamble)
    (hp : p.version = 1#u8 ∧ p.epoch = 1#u64 ∧ p.index = 0#u32 ∧
      p.remaining.val = [0#u8, 0#u8]) :
    msg_preamble b = ok (.Ok p) := by
  obtain ⟨hpv, hpe, hpi, hpr⟩ := hp
  apply msg_preamble_eq_of_blocks b p 1 1 <;>
    simp [alloc.vec.Vec.length, hb, hpv, hpe, hpi, hpr, varintBlockAt, varintVal]

end spqr

namespace spqr.v1.chunked.states.serialize

/-- `Message.serialize` and `msg_preamble` are not injective:

* (a) `Ct1Ack false` and `Ct1Ack true` at epoch `1` have the same serialization, for every
  index `i`. `Message.serialize_spec` shows that `serialize` succeeds, so this is one byte
  string.
* (b) `b₁ = 01 01 00 00` and `b₂ = 01 81 00 00 00` parse to the same preamble `p`, and the body
  of `p` deserializes to `{ epoch := 1, payload := None }`.
* (c) `b₃ = b₁ ++ [00]` parses to a preamble `p₃` that differs from `p` only in `remaining`,
  and the body of `p₃` deserializes to the same message.
* (d) Hence neither `Message.serialize` nor `msg_preamble` is injective. -/
theorem Message.serialize_parse_not_injective
    (i : Std.U32)
    (m₁ m₂ : v1.chunked.states.Message)
    (hm₁ : m₁ = ⟨1#u64, .Ct1Ack false⟩)
    (hm₂ : m₂ = ⟨1#u64, .Ct1Ack true⟩)
    (b₁ b₂ b₃ : alloc.vec.Vec Std.U8)
    (hb₁ : b₁.val = [1#u8, 1#u8, 0#u8, 0#u8])
    (hb₂ : b₂.val = [1#u8, 129#u8, 0#u8, 0#u8, 0#u8])
    (hb₃ : b₃.val = [1#u8, 1#u8, 0#u8, 0#u8, 0#u8])
    (p p₃ : MsgPreamble)
    (hp : p.version = 1#u8 ∧ p.epoch = 1#u64 ∧ p.index = 0#u32 ∧ p.remaining.val = [0#u8])
    (hp₃ : p₃.version = 1#u8 ∧ p₃.epoch = 1#u64 ∧ p₃.index = 0#u32 ∧
      p₃.remaining.val = [0#u8, 0#u8]) :
    (m₁ ≠ m₂ ∧ Message.serialize m₁ i = Message.serialize m₂ i) ∧
    (b₁ ≠ b₂ ∧
      msg_preamble b₁ = ok (.Ok p) ∧ msg_preamble b₂ = ok (.Ok p) ∧
      Message.deserialize p.epoch p.remaining = ok (.Ok ⟨1#u64, .None⟩)) ∧
    (b₁ ≠ b₃ ∧ msg_preamble b₃ = ok (.Ok p₃) ∧
      Message.deserialize p₃.epoch p₃.remaining = ok (.Ok ⟨1#u64, .None⟩)) ∧
    ¬ (∀ (n₁ n₂ : v1.chunked.states.Message) (j : Std.U32),
        Message.serialize n₁ j = Message.serialize n₂ j → n₁ = n₂) ∧
    ¬ (∀ (d₁ d₂ : alloc.vec.Vec Std.U8) (q : MsgPreamble),
        msg_preamble d₁ = ok (.Ok q) → msg_preamble d₂ = ok (.Ok q) → d₁ = d₂) := by
  -- (a)
  have hm : m₁ ≠ m₂ := by subst hm₁ hm₂; simp
  have hser : Message.serialize m₁ i = Message.serialize m₂ i := by
    subst hm₁ hm₂; exact Message.serialize_ct1Ack_eq i 1#u64
  -- The three byte strings are pairwise distinct where the statement needs it.
  have hb₁₂ : b₁ ≠ b₂ := fun h => by
    have := congrArg alloc.vec.Vec.val h; rw [hb₁, hb₂] at this; simp at this
  have hb₁₃ : b₁ ≠ b₃ := fun h => by
    have := congrArg alloc.vec.Vec.val h; rw [hb₁, hb₃] at this; simp at this
  -- (b) and (c)
  have hpre₁ := msg_preamble_minimal_witness b₁ hb₁ p hp
  have hpre₂ := msg_preamble_nonminimal_witness b₂ hb₂ p hp
  have hpre₃ := msg_preamble_trailing_witness b₃ hb₃ p₃ hp₃
  have hdes : Message.deserialize p.epoch p.remaining = ok (.Ok ⟨1#u64, .None⟩) := by
    rw [hp.2.1]; apply deserialize_eq_none <;> simp [hp.2.2.2]
  have hdes₃ : Message.deserialize p₃.epoch p₃.remaining = ok (.Ok ⟨1#u64, .None⟩) := by
    rw [hp₃.2.1]; apply deserialize_eq_none <;> simp [hp₃.2.2.2]
  refine ⟨⟨hm, hser⟩, ⟨hb₁₂, hpre₁, hpre₂, hdes⟩, ⟨hb₁₃, hpre₃, hdes₃⟩, ?_, ?_⟩
  · exact fun h => hm (h m₁ m₂ i hser)
  · exact fun h => hb₁₂ (h b₁ b₂ p hpre₁ hpre₂)

end spqr.v1.chunked.states.serialize

namespace spqr

/-- `recv` cannot tell apart the colliding byte strings of
`v1.chunked.states.serialize.Message.serialize_parse_not_injective`: from any state it
returns the same result on the minimal and the non-minimal encoding, and on the encoding with a
trailing byte. -/
theorem recv_on_witnesses_eq (state b₁ b₂ b₃ : alloc.vec.Vec Std.U8)
    (hb₁ : b₁.val = [1#u8, 1#u8, 0#u8, 0#u8])
    (hb₂ : b₂.val = [1#u8, 129#u8, 0#u8, 0#u8, 0#u8])
    (hb₃ : b₃.val = [1#u8, 1#u8, 0#u8, 0#u8, 0#u8]) :
    recv state b₁ = recv state b₂ ∧ recv state b₁ = recv state b₃ := by
  let p : MsgPreamble := ⟨1#u8, 1#u64, 0#u32, Slice.from [0#u8] (by scalar_tac)⟩
  let p₃ : MsgPreamble := ⟨1#u8, 1#u64, 0#u32, Slice.from [0#u8, 0#u8] (by scalar_tac)⟩
  have hpre₁ := msg_preamble_minimal_witness b₁ hb₁ p (by simp [p])
  have hpre₂ := msg_preamble_nonminimal_witness b₂ hb₂ p (by simp [p])
  have hpre₃ := msg_preamble_trailing_witness b₃ hb₃ p₃ (by simp [p₃])
  have hdes : v1.chunked.states.serialize.Message.deserialize p.epoch p.remaining =
      v1.chunked.states.serialize.Message.deserialize p₃.epoch p₃.remaining := by
    rw [v1.chunked.states.serialize.deserialize_eq_none _ _ (by simp [p]) (by simp [p]),
      v1.chunked.states.serialize.deserialize_eq_none _ _ (by simp [p₃]) (by simp [p₃])]
  exact ⟨recv_eq_of_parse_eq state b₁ b₂ p p hpre₁ hpre₂ rfl rfl rfl rfl,
    recv_eq_of_parse_eq state b₁ b₃ p p₃ hpre₁ hpre₃ rfl rfl rfl hdes⟩

end spqr
