/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs

/-! # Spec theorem for
`spqr::proto::pq_ratchet::{impl core::convert::From<spqr::proto::pq_ratchet::Version> for i32}`
`::from`

Converts `Version` to `i32`: `V0 ↦ 0`, `V1 ↦ 1`.
Inverse of `TryFrom<i32> for Version` on valid discriminants; used by protobuf serialization.

**Source**: generated/signal.proto.pq_ratchet.rs, lines 373:67-373:87 -/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr.I32.Insts.CoreConvertFromVersion

/-- **Spec theorem for `I32.Insts.CoreConvertFromVersion.from`**:

Always succeeds: `V0 ↦ 0`, `V1 ↦ 1`. -/
@[step]
theorem from_spec (value : proto.pq_ratchet.Version) :
    «from» value ⦃ (result : Std.I32) =>
      result = match value with
        | .V0 => 0#iscalar
        | .V1 => 1#iscalar ⦄ := by
  unfold «from»
  cases value <;> simp only [IScalar.cast, IScalarTy.I32_numBits_eq, read_discriminant,
    Bvify.I32.IScalar_bv, BitVec.signExtend_eq,
    BitVec.ofNat_eq_ofNat, WP.spec_ok, IScalar.mk.injEq] <;> decide

end spqr.I32.Insts.CoreConvertFromVersion
