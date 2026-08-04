/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import Aeneas

/-!
# Registration of the `spqr_try_simps` simp attribute

A simp attribute cannot be used in the module that declares it, so the
registration lives here on its own; the lemmas are tagged in
`Spqr.Auxiliary.Aeneas.TrySimps`.
-/

/-- Simp set unfolding the Aeneas translation of Rust's `?`-operator
desugaring (`as_ref`/`ok_or`/`branch`/`from_residual`/`FromSame.from`),
together with the `bind`/`ok` WP reductions needed to push a spec goal
through it. Use as `simp only [spqr_try_simps]` in `from_pb`-style proofs. -/
register_simp_attr spqr_try_simps
