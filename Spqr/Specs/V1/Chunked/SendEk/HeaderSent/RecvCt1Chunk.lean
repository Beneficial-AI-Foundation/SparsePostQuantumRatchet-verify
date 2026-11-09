/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.AddChunk
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.DecodedMessage.DecodedMessage
public import Spqr.Specs.V1.Unchunked.SendEk.EkSent.RecvCt1
import Spqr.Auxiliary.Aeneas.SpecImpExists
/-!
# Spec theorem for
`spqr::v1::chunked::send_ek::{spqr::v1::chunked::send_ek::HeaderSent}::recv_ct1_chunk`

`HeaderSent` is the state of the encapsulation-key-sending (A→B) side of the *chunked* V1
ratchet after A has fully streamed the header to B, while A is still streaming the remainder
of its encapsulation key `ek` to B in fixed-size chunks and is simultaneously collecting the
chunks of B's first ciphertext `ct1`.  It wraps the unchunked state `unchunked::EkSent`
(carrying the current `epoch : u64`, the `Authenticator` and the 2400-byte decapsulation key
`dk`) and adds a `PolyEncoder` that erasure-encodes the outgoing `ek` chunks and a
`PolyDecoder`, sized for `CIPHERTEXT1_SIZE = 960` bytes, that erasure-decodes the incoming
chunks of `ct1`.

`HeaderSent::recv_ct1_chunk` is the transition triggered by a chunk of B's first ciphertext
`ct1`.  On receipt of a 32-byte `Chunk` it:

  1. asserts `epoch == self.uc.epoch` (discharged by the hax contract
     `requires(epoch == self.uc.epoch)`);
  2. feeds the chunk to the decoder (`receiving_ct1.add_chunk(chunk)`), which routes each of the
     16 big-endian GF(2¹⁶) symbols of the chunk to polynomial `j` at x-coordinate `chunk.index`
     and inserts the resulting point into the corresponding sorted set — unless that polynomial
     already holds enough points;
  3. asks the decoder for the reassembled message (`receiving_ct1.decoded_message()`):
       • **`None`** — `ct1` is not yet recoverable; the state is rebuilt with the updated
         decoder and returned as `StillReceiving`;
       • **`Some(decoded)`** — the full `960`-byte `ct1` has been reconstructed.  The unchunked
         `EkSent::recv_ct1` stores it alongside the unchanged `epoch`, `auth` and `dk`, giving
         `unchunked::EkSentCt1Received`; the decoder is dropped (it has served its purpose), the
         encoder `sending_ek` is kept (A may still have `ek` chunks to send), and the result is
         `Done(Ct1Received { uc, sending_ek })`.

No cryptography happens here: `ct1` cannot be authenticated on its own, since the tag received
with `ct2` covers the *complete* ciphertext `ct1 ‖ ct2`; the check is deferred to
`EkSentCt1Received::recv_ct2_chunk`.  In contrast to that transition, the result of
`recv_ct1_chunk` is a plain `HeaderSentRecvChunk` (no `Result` wrapper), because the only
fallible callee, `EkSent::recv_ct1`, merely re-asserts `epoch == self.epoch` — the very
assertion already discharged in step 1 — and is otherwise a pure record construction.

The main theorem `recv_ct1_chunk_spec` follows the predicate-lifting style of
`Specs/Encoding/Decoder/DecodedMessage.lean`: it is parametrised by a postcondition
`decodedPost` for `PolyDecoder::decoded_message` on the updated decoder (hypothesis
`h_decoded`).  `h_decoded` is stated for every decoder `pd` with
`AddChunkPost self.receiving_ct1 chunk pd` and `PointsValid pd.pts` — exactly what
`add_chunk_spec_post` and `add_chunk_spec_valid` guarantee about the updated decoder — so the
registered `decoded_message_spec` can be plugged in.  Note that `AddChunkPost` does *not* pin
down the updated decoder: `IsSortedPushResult` admits both insertion and replacement, so a
decoder related to `self.receiving_ct1` by `AddChunkPost` may differ from the one `add_chunk`
actually produces (and may, e.g., be incomplete where the actual one is complete).  For this
reason `recvCt1ChunkPost` records, in *both* arms, the actual-result equation
`add_chunk self.receiving_ct1 chunk = ok pd` for the retained decoder — not merely
`AddChunkPost` — so that the exported postcondition determines the branch taken from the real
decoder (`recv_ct1_chunk_spec_concrete_done_of_complete`).  Likewise the branch-specific
projections `recv_ct1_chunk_spec_still_receiving` / `recv_ct1_chunk_spec_done` state their
`decoded_message` hypothesis on the *actual* updated decoder rather than on every
`AddChunkPost`-related one (which would make the hypothesis unsatisfiable in the intended
situations).
`recv_ct1_chunk_spec_concrete` instantiates
`decodedPost` with the registered `decoded_message_spec` under the
`#[hax_lib::refine]` invariant of the Rust `HeaderSent`,
`receiving_ct1.pts_needed == CIPHERTEXT1_SIZE / 2`, i.e. `pts_needed = 480`, from which the
decoded `ct1` has exactly `2 · 480 = 960` bytes — the `#[hax_lib::refine(ct1.len() == 960)]`
invariant of `unchunked::EkSentCt1Received` demanded downstream by `recv_ct2`.

All callees (`add_chunk`, `decoded_message`, `recv_ct1`) are discharged by their registered
specs; no opaque constant is involved, since `CIPHERTEXT1_SIZE` is only consulted when the
decoder is *constructed* (`KeysSampled::recv_ct1_chunk`), not here.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 131:4-149:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr encoding.polynomial encoding.gf

/- Helper definitions live in a CamelCase namespace (mirroring
`Spqr.V1.Chunked.SendEk.EkSentCt1Received` in `RecvCt2Chunk.lean`) so that their full names
satisfy the `defsWithUnderscore` linter; the spec theorems themselves stay in the Rust-mirroring
`spqr.v1.chunked.send_ek.HeaderSent` namespace. -/
namespace Spqr.V1.Chunked.SendEk.HeaderSent

open spqr spqr.v1.chunked spqr.v1.chunked.send_ek

/-- Postcondition of `HeaderSent::recv_ct1_chunk` as a predicate on the returned
`HeaderSentRecvChunk`, parametrised by the postcondition `decodedPost` assumed for
`PolyDecoder::decoded_message` on the updated decoder.

  - **`StillReceiving st`** — decoder yields `none`; unchunked state and encoder preserved,
    and the decoder `st.receiving_ct1` is *exactly* the one produced by `add_chunk`
    (`add_chunk self.receiving_ct1 chunk = ok st.receiving_ct1`); it moreover satisfies
    `AddChunkPost` and is still `PointsValid`.
  - **`Done st`** — decoder yields `some ct1`; the encoder is preserved and the unchunked state
    is `recvCt1Result self.uc ct1`, i.e. `self.uc` with the decoded `ct1` stored alongside
    (`epoch`, `auth` and `dk` untouched).  The updated decoder `pd` that produced `ct1` is
    existentially retained together with the equation `add_chunk self.receiving_ct1 chunk = ok pd`
    so that `decodedPost pd (some ct1)` can be exploited by callers.

  The actual-result equations are essential: `AddChunkPost` alone does not determine the
  updated decoder (it admits replacing a point at a different index, e.g. `[0..28] ↦
  [0..27, 29]`), so a postcondition stated only in terms of `AddChunkPost` would still permit
  `StillReceiving` when the incoming chunk supplies the final missing points.  With the
  equation, the branch taken is a function of the decoder `add_chunk` actually produces (see
  `recv_ct1_chunk_spec_concrete_done_of_complete`). -/
def recvCt1ChunkPost (self : HeaderSent) (chunk : encoding.Chunk)
    (decodedPost : PolyDecoder → Option (alloc.vec.Vec U8) → Prop)
    (result : HeaderSentRecvChunk) : Prop :=
  match result with
  | .StillReceiving st =>
      st.uc = self.uc ∧
      st.sending_ek = self.sending_ek ∧
      PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk self.receiving_ct1 chunk =
        ok st.receiving_ct1 ∧
      PolyDecoder.Insts.SpqrEncodingDecoder.AddChunkPost self.receiving_ct1 chunk
        st.receiving_ct1 ∧
      PolyDecoder.PointsValid st.receiving_ct1.pts ∧
      decodedPost st.receiving_ct1 none
  | .Done st =>
      ∃ (pd : PolyDecoder) (ct1 : alloc.vec.Vec U8),
        PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk self.receiving_ct1 chunk = ok pd ∧
        PolyDecoder.Insts.SpqrEncodingDecoder.AddChunkPost self.receiving_ct1 chunk pd ∧
        PolyDecoder.PointsValid pd.pts ∧
        decodedPost pd (some ct1) ∧
        st.sending_ek = self.sending_ek ∧
        st.uc = Spqr.V1.Unchunked.SendEk.EkSent.recvCt1Result self.uc ct1

end Spqr.V1.Chunked.SendEk.HeaderSent

namespace spqr.v1.chunked.send_ek.HeaderSent

open Spqr.V1.Chunked.SendEk.HeaderSent

/-- **Spec theorem for `spqr.v1.chunked.send_ek.HeaderSent.recv_ct1_chunk`**:

• Takes a chunked `HeaderSent` state `self`, consisting of the unchunked inner state
  `self.uc : unchunked.send_ek.EkSent`, the chunk encoder `self.sending_ek : PolyEncoder` and
  the chunk decoder `self.receiving_ct1 : PolyDecoder`, the epoch `epoch : U64` announced by
  the peer, and the received 32-byte `chunk`.  In the original Rust source `self` is consumed
  by value and `chunk` is passed by shared reference; after Aeneas extraction both are plain
  values.
• Checks `massert (epoch = self.uc.epoch)`, which succeeds because of `h_epoch`.
• Absorbs the chunk into the decoder via `add_chunk`, obtaining `receiving_ct1` with
  `AddChunkPost self.receiving_ct1 chunk receiving_ct1`, then queries `decoded_message`,
  obtaining `o : Option (Vec U8)` with `decodedPost receiving_ct1 o`.
• If `o = none`, returns `StillReceiving { self with receiving_ct1 }`.
• If `o = some ct1`, calls `unchunked.send_ek.EkSent.recv_ct1 self.uc epoch ct1`, whose own
  `massert (epoch = self.uc.epoch)` is discharged by the same `h_epoch`, and returns
  `Done { uc := recvCt1Result self.uc ct1, sending_ek := self.sending_ek }`.

• Requires:
    – `h_epoch : epoch = self.uc.epoch` — the hax precondition, discharging both `assert_eq!`s;
    – `h_push_cap` — the `usize` capacity guard of `add_chunk_spec`: each of the 16 sorted
      sets has room for 16 more points; the other guard of `add_chunk_spec`, that the base
      index `chunk.index * 16 + 16` fits in `usize`, holds unconditionally because
      `chunk.index : U16` gives `chunk.index * 16 + 16 ≤ 2¹⁶·16 ≤ Usize.max` on both
      platform widths, and is discharged by `scalar_tac`;
    – `h_valid` — every slot of `self.receiving_ct1.pts` is `SlotSorted` (the `SortedSet`
      invariant), which `add_chunk_spec_valid` carries to the updated decoder;
    – `h_decoded` — the assumed behaviour of `decoded_message` on the decoder `pd` actually
      produced by `add_chunk` (`add_chunk self.receiving_ct1 chunk = ok pd`), which moreover
      satisfies `AddChunkPost self.receiving_ct1 chunk pd` and `PointsValid pd.pts`; callers
      that only need these two consequences (e.g. `recv_ct1_chunk_spec_concrete`) simply
      ignore the equation, while the branch-specific projections rely on it.
  Under these hypotheses the call never panics.  No length hypothesis on the decoded `ct1` is
  needed: `EkSent::recv_ct1` only asserts the epoch (the `ct1.len() == 960` conjunct of its hax
  contract is a struct refinement, see `recv_ct1_chunk_spec_done_wellFormed`).
• The chunked wrapper introduces no epoch logic of its own: on both paths the epoch, the
  authenticator and `dk` of the unchunked state are untouched; on the `Done` path the only
  change is that the decoded `ct1` is stored.

The result satisfies `recvCt1ChunkPost self chunk decodedPost result`.

The proof unfolds `recv_ct1_chunk`, discharges the assertion with `h_epoch`, inverts
`add_chunk_spec_post` conjoined with `add_chunk_spec_valid` (via `spec_imp_exists`) to name the
updated decoder, runs the lifted `h_decoded`, and performs case analysis on the decoded option;
the `some` arm is closed by `recv_ct1_spec`.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 131:4-149:5)
-/
@[step]
theorem recv_ct1_chunk_spec (self : HeaderSent) (epoch : U64) (chunk : encoding.Chunk)
    (decodedPost : PolyDecoder → Option (alloc.vec.Vec U8) → Prop)
    (h_epoch : epoch = self.uc.epoch)
    (h_push_cap : ∀ (k : Nat), k < 16 →
      (self.receiving_ct1.pts[k]!).length + 17 ≤ Usize.max)
    (h_valid : PolyDecoder.PointsValid self.receiving_ct1.pts)
    (h_decoded : ∀ (pd : PolyDecoder),
      PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk self.receiving_ct1 chunk = ok pd →
      PolyDecoder.Insts.SpqrEncodingDecoder.AddChunkPost self.receiving_ct1 chunk pd →
      PolyDecoder.PointsValid pd.pts →
      PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message pd ⦃
        (o : Option (alloc.vec.Vec U8)) => decodedPost pd o ⦄) :
    recv_ct1_chunk self epoch chunk ⦃ (result : HeaderSentRecvChunk) =>
      recvCt1ChunkPost self chunk decodedPost result ⦄ := by
  unfold recv_ct1_chunk
  step with massert_spec _ h_epoch
  obtain ⟨receiving_ct1, h_ok, h_add, h_valid'⟩ := WP.spec_imp_exists (WP.spec_and
    (PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_spec_post self.receiving_ct1 chunk
      (by scalar_tac) h_push_cap)
    (PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_spec_valid self.receiving_ct1 chunk
      (by scalar_tac) h_push_cap h_valid))
  rw [h_ok, bind_ok]
  step with h_decoded receiving_ct1 h_ok h_add h_valid'
  cases o with
  | none =>
    simp only [WP.spec_ok, recvCt1ChunkPost, true_and]
    exact ⟨h_ok, h_add, h_valid', o_post⟩
  | some ct1 =>
    step with unchunked.send_ek.EkSent.recv_ct1_spec self.uc epoch ct1 h_epoch as ⟨uc, h_uc⟩
    simp only [recvCt1ChunkPost, true_and]
    exact ⟨receiving_ct1, ct1, h_ok, h_add, h_valid', o_post, h_uc⟩

/-- **Spec theorem for `spqr.v1.chunked.send_ek.HeaderSent.recv_ct1_chunk`**
(still-receiving case):

If the updated decoder yields no message yet (`decoded_message` returns `none`), the call
returns `StillReceiving st` with the unchunked state and the encoder untouched and the decoder
advanced by `AddChunkPost`.  The hypothesis `h_decoded_none` is stated on the decoder `pd`
*actually* produced by `add_chunk` (`add_chunk self.receiving_ct1 chunk = ok pd`) — not on
every `AddChunkPost`-related decoder, since `AddChunkPost` alone does not determine the updated
points (see the module docstring) and would make the hypothesis unsatisfiable whenever some
`AddChunkPost`-related decoder happens to be complete.  Projection of `recv_ct1_chunk_spec`
with `decodedPost := fun _ o => o = none`.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 131:4-149:5)
-/
theorem recv_ct1_chunk_spec_still_receiving (self : HeaderSent) (epoch : U64)
    (chunk : encoding.Chunk)
    (h_epoch : epoch = self.uc.epoch)
    (h_push_cap : ∀ (k : Nat), k < 16 →
      (self.receiving_ct1.pts[k]!).length + 17 ≤ Usize.max)
    (h_valid : PolyDecoder.PointsValid self.receiving_ct1.pts)
    (h_decoded_none : ∀ (pd : PolyDecoder),
      PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk self.receiving_ct1 chunk = ok pd →
      PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message pd ⦃
        (o : Option (alloc.vec.Vec U8)) => o = none ⦄) :
    recv_ct1_chunk self epoch chunk ⦃ (result : HeaderSentRecvChunk) =>
      ∃ st : HeaderSent,
        result = .StillReceiving st ∧
        st.uc = self.uc ∧
        st.sending_ek = self.sending_ek ∧
        PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk self.receiving_ct1 chunk =
          ok st.receiving_ct1 ∧
        PolyDecoder.Insts.SpqrEncodingDecoder.AddChunkPost self.receiving_ct1 chunk
          st.receiving_ct1 ∧
        PolyDecoder.PointsValid st.receiving_ct1.pts ⦄ := by
  apply WP.spec_mono (recv_ct1_chunk_spec self epoch chunk (fun _ o => o = none) h_epoch
    h_push_cap h_valid (fun pd h_ok _ _ => h_decoded_none pd h_ok))
  intro result h
  match result with
  | .StillReceiving st =>
    obtain ⟨h_uc, h_ek, h_ok, h_add, h_pv, _⟩ := h
    exact ⟨st, rfl, h_uc, h_ek, h_ok, h_add, h_pv⟩
  | .Done _ =>
    obtain ⟨_, _, _, _, _, h_some, _⟩ := h
    exact absurd h_some (by simp)

/-- **Spec theorem for `spqr.v1.chunked.send_ek.HeaderSent.recv_ct1_chunk`**
(decoded case):

If the updated decoder yields a message (`decoded_message` returns `some ct1`), the call
returns `Done st` with the encoder untouched and the unchunked state advanced to
`EkSentCt1Received { epoch := self.uc.epoch, auth := self.uc.auth, dk := self.uc.dk, ct1 }`;
the decoded `ct1` satisfies whatever `decodedProp` the lifted postcondition guarantees.
The hypothesis `h_decoded_some` is stated on the decoder `pd` *actually* produced by
`add_chunk` (`add_chunk self.receiving_ct1 chunk = ok pd`) — not on every
`AddChunkPost`-related decoder: `AddChunkPost` admits replacing a point at a different index
(e.g. `[0..28]` ↦ `[0..27, 29]`), so an `AddChunkPost`-related decoder may remain incomplete
although the actual one is complete, which would make the hypothesis unsatisfiable in exactly
the intended completion case.  Projection of `recv_ct1_chunk_spec` with
`decodedPost := fun _ o => ∃ ct1, o = some ct1 ∧ decodedProp ct1`.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 131:4-149:5)
-/
theorem recv_ct1_chunk_spec_done (self : HeaderSent) (epoch : U64) (chunk : encoding.Chunk)
    (decodedProp : alloc.vec.Vec U8 → Prop)
    (h_epoch : epoch = self.uc.epoch)
    (h_push_cap : ∀ (k : Nat), k < 16 →
      (self.receiving_ct1.pts[k]!).length + 17 ≤ Usize.max)
    (h_valid : PolyDecoder.PointsValid self.receiving_ct1.pts)
    (h_decoded_some : ∀ (pd : PolyDecoder),
      PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk self.receiving_ct1 chunk = ok pd →
      PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message pd ⦃
        (o : Option (alloc.vec.Vec U8)) => ∃ ct1, o = some ct1 ∧ decodedProp ct1 ⦄) :
    recv_ct1_chunk self epoch chunk ⦃ (result : HeaderSentRecvChunk) =>
      ∃ (st : Ct1Received) (ct1 : alloc.vec.Vec U8),
        result = .Done st ∧
        decodedProp ct1 ∧
        st.sending_ek = self.sending_ek ∧
        st.uc.epoch = self.uc.epoch ∧
        st.uc.auth = self.uc.auth ∧
        st.uc.dk = self.uc.dk ∧
        st.uc.ct1 = ct1 ⦄ := by
  apply WP.spec_mono (recv_ct1_chunk_spec self epoch chunk
    (fun _ o => ∃ ct1, o = some ct1 ∧ decodedProp ct1) h_epoch h_push_cap h_valid
    (fun pd h_ok _ _ => h_decoded_some pd h_ok))
  intro result h
  match result with
  | .StillReceiving _ =>
    obtain ⟨_, _, _, _, _, _, h_eq, _⟩ := h
    exact absurd h_eq (by simp)
  | .Done st =>
    obtain ⟨_, ct1, _, _, _, ⟨ct1', h_eq, h_prop⟩, h_ek, h_uc⟩ := h
    simp only [Option.some.injEq] at h_eq; subst h_eq
    exact ⟨st, ct1, rfl, h_prop, h_ek, by rw [h_uc]; rfl, by rw [h_uc]; rfl, by rw [h_uc]; rfl,
      by rw [h_uc]; rfl⟩

/-- **Spec theorem for `spqr.v1.chunked.send_ek.HeaderSent.recv_ct1_chunk`**
(concrete `decoded_message` semantics):

Instantiation of `recv_ct1_chunk_spec` with the registered `decoded_message_spec` instead of a
lifted `decodedPost`.  Besides the hypotheses shared with `recv_ct1_chunk_spec`, it assumes the
`#[hax_lib::refine]` struct invariant of the Rust `HeaderSent`,
`h_pts_needed : self.receiving_ct1.pts_needed = 480` (= `CIPHERTEXT1_SIZE / 2`), which
discharges the output-capacity guard `2 * pts_needed ≤ Usize.max` of `decoded_message_spec`.
The resulting `decodedPost` is exactly the postcondition of `decoded_message_spec`: `none` iff
the decoder is complete or some slot lacks points; `some ct1` with `ct1.length = 960` and
`BytesDecode pd.pts pd.pts_needed ct1.val 0` otherwise.

Because `recvCt1ChunkPost` pins the updated decoder to the one `add_chunk` actually returns
(`add_chunk self.receiving_ct1 chunk = ok pd`), the branch is *determined*: `StillReceiving`
is only permitted when the actual decoder is complete or still misses points, and `Done` only
when it is not.  See `recv_ct1_chunk_spec_concrete_done_of_complete` for the completion case.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 131:4-149:5)
-/
@[step]
theorem recv_ct1_chunk_spec_concrete (self : HeaderSent) (epoch : U64) (chunk : encoding.Chunk)
    (h_epoch : epoch = self.uc.epoch)
    (h_push_cap : ∀ (k : Nat), k < 16 →
      (self.receiving_ct1.pts[k]!).length + 17 ≤ Usize.max)
    (h_valid : PolyDecoder.PointsValid self.receiving_ct1.pts)
    (h_pts_needed : self.receiving_ct1.pts_needed.val = 480) :
    recv_ct1_chunk self epoch chunk ⦃ (result : HeaderSentRecvChunk) =>
      recvCt1ChunkPost self chunk
        (fun pd o =>
          pd.pts_needed.val = 480 ∧
          match o with
          | none => pd.is_complete = true ∨
              PolyDecoder.Insts.SpqrEncodingDecoder.someIncomplete pd.pts pd.pts_needed 0 16
          | some out => pd.is_complete = false ∧
              ¬ PolyDecoder.Insts.SpqrEncodingDecoder.someIncomplete pd.pts pd.pts_needed 0 16 ∧
              out.length = 2 * pd.pts_needed.val ∧
              PolyDecoder.Insts.SpqrEncodingDecoder.BytesDecode pd.pts pd.pts_needed out.val 0)
        result ⦄ := by
  apply recv_ct1_chunk_spec self epoch chunk _ h_epoch h_push_cap h_valid
  intro pd _ h_add h_pv
  have h_pn' : pd.pts_needed.val = 480 := by rw [h_add.1, h_pts_needed]
  apply WP.spec_mono (PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message_spec pd h_pv
    (by rw [h_pn']; scalar_tac))
  intro o h
  exact ⟨h_pn', h⟩

/-- **Spec theorem for `spqr.v1.chunked.send_ek.HeaderSent.recv_ct1_chunk`**
(progress in the completion case):

If the decoder `pd` that `add_chunk` *actually* produces from `self.receiving_ct1` and `chunk`
is not yet marked complete and no slot lacks points (`¬ someIncomplete pd.pts pd.pts_needed
0 16`), then the call **must** return `Done st`, with the encoder untouched and
`st.uc = recvCt1Result self.uc ct1` for a `ct1` of `960` bytes decoding `pd.pts`.

This closes the specification gap left by `AddChunkPost` alone: `AddChunkPost` admits replacing
an existing point (e.g. `[0..28] ↦ [0..27, 29]`), so a decoder merely *related* to the input by
`AddChunkPost` may remain incomplete even when the real one is complete.  Since
`recvCt1ChunkPost` records the actual-result equation `add_chunk self.receiving_ct1 chunk = ok
pd`, the `StillReceiving` arm of `recv_ct1_chunk_spec_concrete` is refuted by determinism of
`add_chunk` whenever the hypothesis `h_complete` holds on the actual decoder.  Projection of
`recv_ct1_chunk_spec_concrete`.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 131:4-149:5)
-/
theorem recv_ct1_chunk_spec_concrete_done_of_complete (self : HeaderSent) (epoch : U64)
    (chunk : encoding.Chunk) (pd : PolyDecoder)
    (h_epoch : epoch = self.uc.epoch)
    (h_push_cap : ∀ (k : Nat), k < 16 →
      (self.receiving_ct1.pts[k]!).length + 17 ≤ Usize.max)
    (h_valid : PolyDecoder.PointsValid self.receiving_ct1.pts)
    (h_pts_needed : self.receiving_ct1.pts_needed.val = 480)
    (h_add : PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk self.receiving_ct1 chunk = ok pd)
    (h_complete : pd.is_complete = false ∧
      ¬ PolyDecoder.Insts.SpqrEncodingDecoder.someIncomplete pd.pts pd.pts_needed 0 16) :
    recv_ct1_chunk self epoch chunk ⦃ (result : HeaderSentRecvChunk) =>
      ∃ (st : Ct1Received) (ct1 : alloc.vec.Vec U8),
        result = .Done st ∧
        st.sending_ek = self.sending_ek ∧
        st.uc = Spqr.V1.Unchunked.SendEk.EkSent.recvCt1Result self.uc ct1 ∧
        ct1.length = 960 ∧
        PolyDecoder.Insts.SpqrEncodingDecoder.BytesDecode pd.pts pd.pts_needed ct1.val 0 ⦄ := by
  apply WP.spec_mono (recv_ct1_chunk_spec_concrete self epoch chunk h_epoch
    h_push_cap h_valid h_pts_needed)
  intro result h
  match result with
  | .StillReceiving st =>
    obtain ⟨_, _, h_ok, _, _, _, h_none⟩ := h
    rw [h_add, ok.injEq] at h_ok
    subst h_ok
    rcases h_none with h_c | h_inc
    · exact absurd h_c (by rw [h_complete.1]; decide)
    · exact absurd h_inc h_complete.2
  | .Done st =>
    obtain ⟨pd', ct1, h_ok, _, _, ⟨h_pn, _, _, h_len, h_dec⟩, h_ek, h_uc⟩ := h
    rw [h_add, ok.injEq] at h_ok
    subst h_ok
    exact ⟨st, ct1, rfl, h_ek, h_uc, by rw [h_len, h_pn], h_dec⟩

/-- **Spec theorem for `spqr.v1.chunked.send_ek.HeaderSent.recv_ct1_chunk`**
(well-formedness of the `Done` state):

Under the concrete `decoded_message` semantics and the `#[hax_lib::refine]` invariants of the
input — `pts_needed = 480` for the decoder and `dk.len() == 2400` for the unchunked
`EkSent` — whenever the call returns `Done st`, the unchunked successor `st.uc` satisfies the
`#[hax_lib::refine]` invariants of `unchunked::EkSentCt1Received`, i.e.
`dk.length = 2400 ∧ ct1.length = 960`
(`serialize.EkSentCt1Received.FunctionalModels.WellFormed`), and the encoder is untouched.
These are exactly the `h_dk` / `h_ct1` hypotheses that the follow-up transitions
`Ct1Received::recv_ct2_chunk` and `EkSentCt1Received::recv_ct2_chunk` require.  Projection of
`recv_ct1_chunk_spec_concrete`.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 131:4-149:5)
-/
theorem recv_ct1_chunk_spec_done_wellFormed (self : HeaderSent) (epoch : U64)
    (chunk : encoding.Chunk)
    (h_epoch : epoch = self.uc.epoch)
    (h_push_cap : ∀ (k : Nat), k < 16 →
      (self.receiving_ct1.pts[k]!).length + 17 ≤ Usize.max)
    (h_valid : PolyDecoder.PointsValid self.receiving_ct1.pts)
    (h_pts_needed : self.receiving_ct1.pts_needed.val = 480)
    (h_wf : unchunked.send_ek.serialize.EkSent.FunctionalModels.WellFormed self.uc) :
    recv_ct1_chunk self epoch chunk ⦃ (result : HeaderSentRecvChunk) =>
      ∀ st, result = .Done st →
        st.sending_ek = self.sending_ek ∧
        st.uc.epoch = self.uc.epoch ∧
        unchunked.send_ek.serialize.EkSentCt1Received.FunctionalModels.WellFormed st.uc ⦄ := by
  apply WP.spec_mono (recv_ct1_chunk_spec_concrete self epoch chunk h_epoch
    h_push_cap h_valid h_pts_needed)
  intro result h st h_eq
  subst h_eq
  obtain ⟨_, ct1, _, _, _, ⟨h_pn, _, _, h_len, _⟩, h_ek, h_uc⟩ := h
  rw [h_uc]
  refine ⟨h_ek, rfl, h_wf, ?_⟩
  change ct1.length = 960
  rw [h_len, h_pn]

/-- **Completeness of the precondition of `spqr.v1.chunked.send_ek.HeaderSent.recv_ct1_chunk`**:

The hypothesis `epoch = self.uc.epoch` of `recv_ct1_chunk_spec` is not merely sufficient but
necessary: whenever the announced epoch differs from the stored one, the leading `assert_eq!`
fires before the decoder is touched and the call panics.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 131:4-149:5)
-/
theorem recv_ct1_chunk_fail_of_epoch_ne (self : HeaderSent) (epoch : U64)
    (chunk : encoding.Chunk)
    (h_epoch : epoch ≠ self.uc.epoch) :
    recv_ct1_chunk self epoch chunk = fail Error.assertionFailure := by
  simp only [recv_ct1_chunk, massert, h_epoch, ↓reduceIte, bind_fail]

end spqr.v1.chunked.send_ek.HeaderSent
