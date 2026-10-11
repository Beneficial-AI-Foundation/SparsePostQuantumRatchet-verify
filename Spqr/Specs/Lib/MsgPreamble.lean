/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Chunked.States.Serialize.DecodeVarint
import Spqr.Specs.Aeneas.VecIndexRangeFull
/-!
# Spec theorem for `spqr::msg_preamble`

`msg_preamble` parses the common preamble of a serialized message:

  `[version byte] ++ [varint(epoch)] ++ [varint(index)] ++ remaining`

An empty message yields the default preamble (`version = 0`, `epoch = 0`, `index = 0`, empty
`remaining`). Otherwise the epoch must be nonzero and the index must fit in a `u32`; every
failure is `Error::MsgDecode`.

The varint blocks are stated via `varintBlockAt`, exactly as established by
`decode_varint_spec`.

**Source**: src/lib.rs (lines 563:0-590:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr

open core.result.Result.Insts

/-- Discharge a `?`-propagated error branch. -/
local macro "close_err" : tactic =>
  `(tactic| simp_all only [core.result.Result.map_err_Ok, core.result.Result.map_err_Err,
    msg_preamble.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError,
    msg_preamble.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError.call_once,
    CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok])

private theorem vec_deref_val (v : alloc.vec.Vec U8) : v.deref.val = v.val := by
  simp [alloc.vec.Vec.deref]

/-- **Spec theorem for `spqr.msg_preamble`**:

* Empty message → `Ok` of the default preamble (`version = 0`, `epoch = 0`, `index = 0`,
  `remaining = []`).
* Non-empty message, on success: `version` is the first byte, then come a varint block of
  `n₁` bytes decoding to `epoch ≠ 0` and a varint block of `n₂` bytes decoding to `index`, and
  `remaining` is the rest of the message after these blocks.
* On failure the error is `Error::MsgDecode`.

Never panics. -/
@[step]
theorem msg_preamble_spec (msg : alloc.vec.Vec U8) :
    msg_preamble msg ⦃ (r : core.result.Result MsgPreamble Error) =>
      match r with
      | .Ok p =>
        (msg.length = 0 →
          p.version.val = 0 ∧ p.epoch.val = 0 ∧ p.index.val = 0 ∧ p.remaining.val = []) ∧
        (0 < msg.length →
          p.version = msg.val[0]! ∧ 0 < p.epoch.val ∧
          ∃ n₁ n₂, varintBlockAt msg.val 1 n₁ p.epoch.val ∧
            varintBlockAt msg.val (1 + n₁) n₂ p.index.val ∧
            p.remaining.val = msg.val.drop (1 + n₁ + n₂))
      | .Err e => e = Error.MsgDecode ⦄ := by
  unfold msg_preamble
  simp only [CoreOpsTry.branch]
  step*
  · -- empty message: the default preamble
    have hnil : msg.val = [] := by simp_all [List.isEmpty_iff]
    have hlen : msg.length = 0 := by simp [alloc.vec.Vec.length, hnil]
    refine ⟨fun _ => ⟨rfl, rfl, rfl, ?_⟩, fun h => absurd h (by omega)⟩
    simp_all
  · simp_all [List.length_pos_iff]
  match r with
  | .Err _ => close_err
  | .Ok epochV =>
    obtain ⟨-, n₁, hat₁, hblk₁⟩ :
        1 < msg.deref.length ∧ ∃ n, _ = 1 + n ∧ varintBlockAt (↑msg.deref) 1 n ↑epochV := by
      assumption
    rw [vec_deref_val] at hblk₁
    step*
    match r1 with
    | .Err _ => close_err
    | .Ok idx64 =>
      obtain ⟨-, n₂, hat₂, hblk₂⟩ :
          _ < msg.deref.length ∧ ∃ n, _ = _ + n ∧ varintBlockAt (↑msg.deref) _ n ↑idx64 := by
        assumption
      rw [vec_deref_val, hat₁] at hblk₂
      step*
      match r2 with
      | .Err _ => close_err
      | .Ok idx =>
        obtain ⟨-, hidx⟩ : _ ∧ idx.val = idx64.val := by assumption
        simp only [core.result.Result.map_err_Ok]
        step*
        have hlen : 1 + n₁ ≤ msg.length := hblk₁.2.2.1
        refine ⟨fun h => absurd h (by omega), fun _ => ⟨?_, ?_, n₁, n₂, hblk₁, hidx ▸ hblk₂, ?_⟩⟩
        · rw [‹version = _›, getElem!_pos msg.val 0 (by scalar_tac)]
        · have : epochV.val ≠ 0 := fun h => ‹¬epochV = 0#u64› (UScalar.eq_of_val_eq h)
          omega
        · rw [‹s2.val = _›, hat₂, hat₁]

end spqr
