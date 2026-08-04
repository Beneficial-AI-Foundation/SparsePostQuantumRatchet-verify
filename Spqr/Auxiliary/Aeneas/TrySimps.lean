/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.FunsExternal
import Spqr.Auxiliary.Aeneas.TrySimpsAttr

/-!
# The `spqr_try_simps` simp set

Aeneas translates Rust's `?` operator on an `Option` field into the chain
`as_ref` → `ok_or` → `branch`, with the `Break` arm routed through
`from_residual` and the identity `From` instance `FromSame.from`. This simp
set bundles those unfoldings with the WP reductions `bind_tc_ok` and
`WP.spec_ok`, so a `from_pb`-style proof can discharge the whole chain with
a single `simp only [spqr_try_simps]` (followed by `step*` when a further
call remains on the success path).
-/

attribute [spqr_try_simps]
  core.option.Option.as_ref
  core.option.Option.ok_or
  Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch
  Aeneas.Std.core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
  Aeneas.Std.core.convert.FromSame.from
  Aeneas.Std.bind_tc_ok
  Aeneas.Std.WP.spec_ok
