/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs

/-! # Spec theorem for
`spqr::proto::pq_ratchet::{impl core::convert::From<spqr::proto::pq_ratchet::Direction> for i32}`
`::from`

Converts `Direction` to `i32`: `A2B ↦ 0`, `B2A ↦ 1`.
Inverse of `TryFrom<i32> for Direction` on valid discriminants; used by protobuf serialization.

**Source**: generated/signal.proto.pq_ratchet.rs, lines 400:67-400:87 -/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr.I32.Insts.CoreConvertFromDirection

/-- **Spec theorem for `I32.Insts.CoreConvertFromDirection.from`**:

Always succeeds: `A2B ↦ 0`, `B2A ↦ 1`. -/
@[step]
theorem from_spec (value : proto.pq_ratchet.Direction) :
    «from» value ⦃ (result : Std.I32) =>
      result = match value with
        | .A2B => 0#iscalar
        | .B2A => 1#iscalar ⦄ := by
  unfold «from»
  cases value <;> simp only [IScalar.cast, IScalarTy.I32_numBits_eq, read_discriminant,
    Bvify.I32.IScalar_bv, BitVec.signExtend_eq,
    BitVec.ofNat_eq_ofNat, WP.spec_ok, IScalar.mk.injEq] <;> decide

end spqr.I32.Insts.CoreConvertFromDirection
