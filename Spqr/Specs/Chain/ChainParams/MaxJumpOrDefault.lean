/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.DEFAULT_CHAIN_PARAMS
/-!
# Spec theorem for `spqr::chain::{spqr::proto::pq_ratchet::ChainParams}::max_jump_or_default`

Protobuf message types follow the convention that every field defaults to zero when it is not
explicitly set on the wire.  A literal `max_jump = 0` is therefore ambiguous: it may mean "the
sender genuinely wants a zero jump budget" or "the sender left the field unset".  The library
resolves this ambiguity by treating zero as *unset* and substituting the compile-time default.

`max_jump_or_default` implements exactly this getter policy for the `max_jump` field:

  * if the stored `max_jump` is strictly positive it is a real, caller-supplied value and is
    returned verbatim;
  * otherwise (i.e. `max_jump = 0`) the library-wide default `DEFAULT_CHAIN_PARAMS.max_jump`
    (= 25 000) is returned instead.

The function performs only a comparison and a field read, so it never allocates and never
overflows: it is total on every `ChainParams` value.

**Source**: spqr/src/chain.rs (lines 68:4-74:5)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.ChainParams

/-- **Spec theorem for `spqr.chain.ChainParams.max_jump_or_default`**:

Reads the maximum forward-jump budget from a protobuf `ChainParams`, applying the "zero means
unset" defaulting convention.  Phrased as biconditionals, the result is fully characterized by
*both* possible outcomes — the verbatim-copy branch and the default branch:

  • `result = self.max_jump ↔ self.max_jump > 0` — the stored value is returned exactly when it
      is a real, caller-supplied (strictly positive) value;
  • `result = DEFAULT_CHAIN_PARAMS.max_jump ↔
        self.max_jump = 0 ∨ self.max_jump = DEFAULT_CHAIN_PARAMS.max_jump` — the library default
      (= 25 000) is the result either when the field is unset (`= 0`, the `else` branch) or when
      the caller happens to have supplied exactly the default value.

The extra `∨ self.max_jump = DEFAULT_CHAIN_PARAMS.max_jump` disjunct is essential for the second
`↔` to hold: when the source field already equals the (non-zero) default, the `then` branch copies
it verbatim, so the result equals the default without the field being zero.

The function always succeeds (no panic): it only performs a single comparison and returns one of
two field values, with no arithmetic that could overflow and no fallible operation of any kind.

The proof unfolds `max_jump_or_default` to expose the guard `self.max_jump > 0#u32` and `split`s on
that conditional.  The `then` branch (`self.max_jump > 0`) closes with `simp_all`.  The `else`
branch (`self.max_jump = 0`) uses `simp_all [DEFAULT_CHAIN_PARAMS_spec]` to evaluate the default's
`max_jump` field, then `scalar_tac` to turn the scalar-value hypothesis `self.max_jump.val = 0`
back into the field equality `self.max_jump = 0#u32`.

**Source**: spqr/src/chain.rs (lines 68:4-74:5)
-/
@[step]
theorem max_jump_or_default_spec (self : proto.pq_ratchet.ChainParams) :
    max_jump_or_default self ⦃ (result : Std.U32) =>
      (result = self.max_jump ↔ self.max_jump > 0#u32) ∧
      (result = chain.DEFAULT_CHAIN_PARAMS.max_jump ↔
        self.max_jump = 0#u32 ∨ self.max_jump = chain.DEFAULT_CHAIN_PARAMS.max_jump) ⦄ := by
  unfold max_jump_or_default
  split
  · simp_all
  · simp_all only [gt_iff_lt, UScalar.lt_equiv, UScalar.ofNatCore_val_eq, not_lt,
    nonpos_iff_eq_zero, DEFAULT_CHAIN_PARAMS_spec, ne_eq, UScalar.neq_to_neq_val,
    iff_false, Nat.not_eq, OfNat.zero_ne_ofNat, not_false_eq_true, OfNat.ofNat_ne_zero,
    Nat.ofNat_pos, not_lt_zero, or_false, or_self, UScalar.val_not_eq_imp_not_eq, WP.spec_ok,
    true_iff, true_and]
    scalar_tac

end spqr.chain.ChainParams
