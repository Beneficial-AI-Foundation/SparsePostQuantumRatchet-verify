/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import Spqr.Specs.Chain.ChainEpochDirection.Key
-- For the private platform-independent cores (`body_spec_core`, `key_loop_spec_core`,
-- `key_spec_all_core`) that the 32-bit theorems instantiate.
import all Spqr.Specs.Chain.ChainEpochDirection.Key

/-! # 32-bit platform variants for `ChainEpochDirection::key`

This file provides 32-bit platform variants of the loop body spec, the loop spec and all the
key specs.  The only differences from the 64-bit versions in `Key.lean` are:

  - The maxOoo bound (and with it the counter bound `U32.max - …`) is tightened from
    `390451572` to `108458770`.  On a 32-bit platform `Usize.max = 2³² − 1`, so the GC trim
    threshold `(maxOoo * 11/10 + 1) * 36` must fit in 32 bits, which requires
    `maxOoo < 108458770`.
  - No `h_platform` hypothesis is needed.

All proofs are instances of the platform-independent cores in `Key.lean`.

**Source**: spqr/src/chain.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr.chain.ChainEpochDirection.key_loop

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.key_loop.body`** (32-bit platform):

One step of the chain-key advancement loop.

- **Done case** (`at1 ≤ i + 1`): the body returns `done (i, v, kh)` with the counter, chain
  secret, and key history all unchanged.
- **Cont case** (`at1 > i + 1`): `next_key_internal` is called, producing an incremented
  counter `i2 = i + 1` and a new HKDF output `okm = nextKeyHkdfOutput v.val (i+1)`.
  The new chain secret satisfies `v2.length = 32` and `v2.val = okm.take 32`.
  The derived key is `k.2.val = okm.drop 32`.
    • If `i2 + max_ooo_keys_or_default(params) ≥ at1`, the key `k` is added to the history:
      `kh2.data.length = kh.data.length + 36` and
      `kh2.data = kh.data ++ to_be_bytes(k.1) ++ k.2`.
    • Otherwise the history is unchanged: `kh2 = kh`.
  In both sub-cases the counter advances: `i2.val = i.val + 1`.

Identical to `body_spec` but with the tighter maxOoo bound `108458770` for 32-bit platforms. -/
@[step]
theorem body_spec_32
    (at1 : U32) (params : proto.pq_ratchet.ChainParams)
    (i : U32) (v : alloc.vec.Vec U8) (kh : chain.KeyHistory)
    (h_v_len : v.length = 32)
    (h_i : i < U32.max)
    (h_kh_cap : kh.data.length + 36 ≤ Usize.max)
    (h_ctr_bound : i.val + 1 ≤ U32.max - 108458770)
    (h_maxooo_bound : (chain.maxOoo params).val < 108458770) :
    body at1 params i v kh ⦃ cf =>
      match cf with
      | ControlFlow.done (i', v', kh') =>
          i' = i ∧ v' = v ∧ kh' = kh ∧ ¬(at1.val > i.val + 1)
      | ControlFlow.cont (i2, v2, kh2) =>
          at1.val > i.val + 1 ∧
          i2.val = i.val + 1 ∧
          v2.length = 32 ∧
          (let okm := nextKeyHkdfOutput v.val (⟨i.val + 1, by scalar_tac⟩ : U32)
           v2.val = okm.take 32) ∧
          (let ctr1 : U32 := ⟨i.val + 1, by scalar_tac⟩
           let okm := nextKeyHkdfOutput v.val ctr1
           if (i.val + 1) + (chain.maxOoo params).val ≥ at1.val then
              kh2.data.length = kh.data.length + 36 ∧
              kh2.data = kh.data ++ (core.num.U32.to_be_bytes ctr1).val ++ okm.drop 32
           else
            kh2 = kh) ⦄ :=
  body_spec_core at1 params i v kh h_v_len h_i h_kh_cap (by omega)

end spqr.chain.ChainEpochDirection.key_loop

/-! # Spec theorem for `spqr::chain::{spqr::chain::ChainEpochDirection}::key`: loop 0 (32-bit)

The full loop spec for the chain-key advancement loop of `ChainEpochDirection::key`.  The loop
iterates from counter `i` up to `at - 1`, repeatedly calling `next_key_internal` to derive the
next chain secret and (conditionally) recording derived keys in the key history.

The loop uses the `loop` fixed-point combinator.  We prove the spec by applying
`loop.spec_decr_nat` with:

  - **Measure**: `at.val - i.val` (strictly decreasing at each iteration since the counter
    advances by 1).
  - **Invariant**: the chain-secret vector has length 32, the counter stays below `U32.max`,
    the key-history capacity bound is maintained, and the counter–maxOoo arithmetic stays
    in range.

On termination the loop returns `(i_final, v_final, kh_final)` where `i_final` is the last
counter value at which `at ≤ i_final + 1` (i.e. `i_final + 1 ≥ at`), `v_final` has length 32,
and `kh_final` is the accumulated key history.

## Properties

1. **Exact counter value**: the final counter satisfies `i_f.val + 1 = max at1.val (i.val + 1)`,
   i.e. `i_f = at1 - 1` when the loop executes and `i_f = i` when it does not.
2. **Chain secret length**: `v_f.length = 32`.
3. **Chain secret value**: the final chain secret equals `iterChainSecret v.val i.val steps`
   where `steps = at1.val - (i.val + 1)` (clamped to 0).  This captures the functional
   correctness of iterated HKDF derivation.
4. **Key history content**: the final key history equals
   `iterKeyHistory v.val i.val at1.val params kh steps`, i.e. exactly the keys that
   `next_key_internal` derived during the loop, selectively recorded based on the
   `maxOoo` proximity check.
5. **Key history bounds**: the key history can only grow, and grows by at most 36 bytes per
   iteration: `kh.data.length ≤ kh_f.data.length ≤ kh.data.length + 36 * (at1.val - i.val)`.
6. **Zero-iteration identity**: when `at1.val ≤ i.val + 1` the state is returned unchanged:
   `i_f = i ∧ v_f = v ∧ kh_f = kh`.

Identical to `key_loop_spec` but with the tighter maxOoo bound `108458770` for 32-bit platforms.

**Source**: spqr/src/chain.rs, lines 270:8-286:9 -/

namespace spqr.chain.ChainEpochDirection

@[step]
theorem key_loop_spec_32
    (at1 : U32) (params : proto.pq_ratchet.ChainParams)
    (i : U32) (v : alloc.vec.Vec U8) (kh : chain.KeyHistory)
    (h_v_len : v.length = 32)
    (h_at_bound : at1.val ≤ U32.max - 108458770)
    (h_maxooo_bound : (chain.maxOoo params).val < 108458770)
    (h_kh_cap : kh.data.length + 36 * (at1.val - i.val) ≤ Usize.max)
    (h_i_bound : i.val < U32.max) :
    key_loop i v kh at1 params ⦃ (result : U32 × (alloc.vec.Vec U8) × chain.KeyHistory) =>
      let steps := at1.val - (i.val + 1)
      result.1.val + 1 = Nat.max at1.val (i.val + 1) ∧
      result.2.1.length = 32 ∧
      result.2.1.val = iterChainSecret v.val i.val steps ∧
      result.2.2 = iterKeyHistory v.val i.val at1.val params kh steps ∧
      kh.data.length ≤ result.2.2.data.length ∧
      result.2.2.data.length ≤ kh.data.length + 36 * (at1.val - i.val) ∧
      (at1.val ≤ i.val + 1 → result.1 = i ∧ result.2.1 = v ∧ result.2.2 = kh) ⦄ :=
  key_loop_spec_core at1 params i v kh h_v_len (by scalar_tac) h_kh_cap h_i_bound

/-- **Combined spec for all branches of `key`** (32-bit platform): the full postcondition
`chain.cedKeyPost`, as an instance of `key_spec_all_core`.  The per-branch theorems below
are projections of this one. -/
private theorem key_spec_all_32 (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (_h_at_bound : ats.val ≤ U32.max - 108458770)
    (h_maxooo_bound : (chain.maxOoo params).val < 108458770)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_bound : self.prev.data.length ≤ Usize.max)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max) :
    key self ats params ⦃ (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
      chain.cedKeyPost self ats params result.1 result.2 ⦄ := by
  have h_raw := maxOoo_imp_raw_ooo params _ h_maxooo_bound
  exact key_spec_all_core self ats params h_next_len (by omega) (by scalar_tac) h_kh_cap
    h_prev_aligned h_prev_bound h_prev_ctr h_ooo_no_overflow

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.key`** (32-bit platform, equal case):

• Takes a `ChainEpochDirection` value `self`, a target counter `ats`, and chain parameters
  `params`.
• Proves the **equal case** (`ats = self.ctr`): the function returns
  `(Err (Error.KeyAlreadyRequested ats), self)` — the key has already been consumed.

Identical to `key_spec_equal` but with:
  - `h_at_bound : ats.val ≤ U32.max - 108458770` (tighter bound for 32-bit)
  - `h_maxooo_bound : (chain.maxOoo params).val < 108458770`
  - No `h_platform` hypothesis required.

**Source**: spqr/src/chain.rs, lines 247:4-296:5
-/
@[step]
theorem key_spec_equal_32 (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 108458770)
    (h_maxooo_bound : (chain.maxOoo params).val < 108458770)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_bound : self.prev.data.length ≤ Usize.max)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max) :
    key self ats params ⦃ (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
        -- Equal case: key already requested
      (ats = self.ctr →
          result.1 = core.result.Result.Err (Error.KeyAlreadyRequested ats) ∧
          result.2 = self) ⦄ := by
  apply WP.spec_mono (key_spec_all_32 self ats params h_next_len h_at_bound h_maxooo_bound
    h_kh_cap h_prev_aligned h_prev_bound h_prev_ctr h_ooo_no_overflow)
  exact fun _ h => h.1

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.key`** (32-bit platform, greater case):

Proves that when `ats > self.ctr` and the jump exceeds `max_jump_or_default(params)`, the function
returns `(Err (Error.KeyJump self.ctr ats), self)` with the state unchanged.

Identical to `key_spec_greater` but with the tighter maxOoo bound `108458770` and no `h_platform`
hypothesis.

**Source**: spqr/src/chain.rs, lines 247:4-296:5
-/
@[step]
theorem key_spec_greater_32 (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 108458770)
    (h_maxooo_bound : (chain.maxOoo params).val < 108458770)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_bound : self.prev.data.length ≤ Usize.max)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max) :
    key self ats params ⦃
      (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
      (ats > self.ctr →
          ats.val - self.ctr.val > (chain.maxJump params).val →
          result.1 = core.result.Result.Err (Error.KeyJump self.ctr ats) ∧
          result.2 = self) ⦄ := by
  apply WP.spec_mono (key_spec_all_32 self ats params h_next_len h_at_bound h_maxooo_bound
    h_kh_cap h_prev_aligned h_prev_bound h_prev_ctr h_ooo_no_overflow)
  exact fun _ h => h.2.2.1

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.key`** (32-bit platform, less case):

Proves the **less case** (`ats < self.ctr`): delegates to `KeyHistory.get` to retrieve a
previously-stored key. In all sub-cases, `result.2.ctr = self.ctr` and
`result.2.next = self.next` (only `prev` is modified). The domain-level result is one of:
  - `Err (Error.KeyTrimmed ats)` when `ats + maxOoo params < self.ctr`
    (key was garbage-collected), with `self.prev` unchanged.
  - `Err (Error.KeyAlreadyRequested ats)` when the key is within the OOO window but not found
    in history, with `self.prev` unchanged.
  - `Ok out` with `out.length = 32`, key found and removed from history
    (`result.2.prev.data.length = self.prev.data.length - 36`), and provenance:
    there exists a 36-aligned offset `off` in `self.prev.data` whose 4-byte tag matches `ats`
    and whose 32-byte payload equals `out`.

Identical to `key_spec_less` but with the tighter maxOoo bound `108458770` and no `h_platform`
hypothesis.

**Source**: spqr/src/chain.rs, lines 247:4-296:5
-/
@[step]
theorem key_spec_less_32 (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 108458770)
    (h_maxooo_bound : (chain.maxOoo params).val < 108458770)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_bound : self.prev.data.length ≤ Usize.max)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max) :
    key self ats params ⦃
      (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
      (ats < self.ctr →
          chain.cedKeyLessPost self ats params result.1 result.2) ⦄ := by
  apply WP.spec_mono (key_spec_all_32 self ats params h_next_len h_at_bound h_maxooo_bound
    h_kh_cap h_prev_aligned h_prev_bound h_prev_ctr h_ooo_no_overflow)
  exact fun _ h => h.2.1

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.key`** (32-bit platform, greater-jump case):

Proves the **greater case with jump within budget** (`ats > self.ctr` and
`ats.val - self.ctr.val ≤ max_jump_or_default(params)`). Projection of
`key_spec_all_32`.

Identical to `key_spec_greater_jump` but with the tighter maxOoo bound `108458770` and no
`h_platform` hypothesis.

**Source**: spqr/src/chain.rs, lines 247:4-296:5
-/
@[step]
theorem key_spec_greater_jump_32 (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 108458770)
    (h_maxooo_bound : (chain.maxOoo params).val < 108458770)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_bound : self.prev.data.length ≤ Usize.max)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max) :
    key self ats params ⦃
      (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
      (∀ (h_gt : ats > self.ctr),
          ats.val - self.ctr.val ≤ (chain.maxJump params).val →
          chain.cedKeyAdvancePost self ats params result.1 result.2 h_gt) ⦄ := by
  apply WP.spec_mono (key_spec_all_32 self ats params h_next_len h_at_bound h_maxooo_bound
    h_kh_cap h_prev_aligned h_prev_bound h_prev_ctr h_ooo_no_overflow)
  exact fun _ h => h.2.2.2

/-- **Combined spec theorem for `spqr.chain.ChainEpochDirection.key`** (32-bit platform):

Combines the equal, less, greater, and greater-jump cases into a single postcondition
`chain.cedKeyPost self ats params result.1 result.2`.

Identical to `key_spec` but with the tighter maxOoo bound `108458770` and no `h_platform`
hypothesis.

**Source**: spqr/src/chain.rs, lines 247:4-296:5
-/
@[step]
theorem key_spec_32 (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 108458770)
    (h_maxooo_bound : (chain.maxOoo params).val < 108458770)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_bound : self.prev.data.length ≤ Usize.max)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max) :
    key self ats params ⦃ (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
      chain.cedKeyPost self ats params result.1 result.2 ⦄ := by
  exact key_spec_all_32 self ats params h_next_len h_at_bound h_maxooo_bound
    h_kh_cap h_prev_aligned h_prev_bound h_prev_ctr h_ooo_no_overflow

end spqr.chain.ChainEpochDirection
