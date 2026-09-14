/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.Chain.CedForDirection
import Spqr.Specs.Lib.Direction.Switch
import Spqr.Specs.Kdf.HkdfToSlice
import Spqr.Crypto.Hkdf
/-!
# Spec theorem for `spqr::chain::{spqr::chain::Chain}::new`

Constructs a `Chain` from `initial_key`, `dir`, and `params` by deriving 96 bytes via
HKDF-SHA256 (zero salt, chain-start info), splitting into `next_root`, send/recv keys
by direction, and returning an epoch-0 chain with a single-element deque.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr.chain.Chain

/-- **Spec theorem for `spqr.chain.Chain.new`**:

Derives `genr8r` via HKDF-SHA256 from `initial_key` (zero salt, chain-start info).
Returns `Ok(Chain)` with `current_epoch = send_epoch = 0`, `next_root = genr8r[0..32]`,
and a single `ChainEpoch` whose send/recv keys are direction-dependent 32-byte slices
of `genr8r`. Postcondition covers both structural fields and cryptographic content. -/
@[step]
theorem new_spec (initial_key : Slice U8) (dir : proto.pq_ratchet.Direction)
    (params : proto.pq_ratchet.ChainParams) :
    new initial_key dir params ⦃ (result : core.result.Result chain.Chain Error) =>
      let genr8r := newHkdfOutput initial_key.val
      match result with
      | .Ok chain =>
          chain.dir = dir ∧
          chain.current_epoch = 0#u64 ∧
          chain.send_epoch = 0#u64 ∧
          chain.params = params ∧
          chain.next_root.val = genr8r.slice 0 32 ∧
          chain.next_root.length = 32 ∧
          chain.links.length = 1#usize ∧
          chain.links.head = 0#usize ∧
          match chain.links.buf.val with
          | [epoch] =>
            epoch.send.ctr = 0#u32 ∧
            epoch.send.prev.data.length = 0 ∧
            epoch.send.next.val = (match dir with
              | .A2B => genr8r.slice 32 64
              | .B2A => genr8r.slice 64 96) ∧
            epoch.send.next.length = 32 ∧
            epoch.recv.ctr = 0#u32 ∧
            epoch.recv.prev.data.length = 0 ∧
            epoch.recv.next.val = (match dir with
              | .A2B => genr8r.slice 64 96
              | .B2A => genr8r.slice 32 64) ∧
            epoch.recv.next.length = 32
          | _ => False
      | .Err _ => False ⦄ := by
  unfold new
  match dir with
  | .A2B =>
    step*
    · grind
    · simp_all [Array.make, newHkdfOutput, chainStartLabel, crypto.zeroSalt32]
      constructor <;> simp [List.slice_length, crypto.hkdf_length]
  | .B2A =>
    step*
    · grind
    · simp_all [Array.make, newHkdfOutput, chainStartLabel, crypto.zeroSalt32]
      constructor <;> simp [List.slice_length, crypto.hkdf_length]

end spqr.chain.Chain
