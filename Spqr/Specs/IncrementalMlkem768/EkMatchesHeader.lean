/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import SrcTranslated.Funs
public import SrcTranslated.FunsExternal
/-!
# Spec theorem for `spqr::incremental_mlkem768::ek_matches_header`

`ek_matches_header` checks whether a given ML-KEM-768 encapsulation key `ek` is consistent with
a header `hdr`.  It delegates to `libcrux_ml_kem::mlkem768::incremental::validate_pk_bytes`,
passing the header and encapsulation key byte slices, and returns `true` if and only if
validation succeeds (i.e. the inner `Result` is `Ok`).

The Rust source is simply:

```
pub fn ek_matches_header(ek: &EncapsulationKey, hdr: &Header) -> bool {
    incremental::validate_pk_bytes(hdr, ek).is_ok()
}
```

The extracted Lean body (`SrcTranslated/Funs.lean`, lines 10059–10064) mirrors this:
it dereferences both vectors, calls `validate_pk_bytes`, and then `Result.is_ok` on the
inner `core.result.Result`.

**Source**: `src/incremental_mlkem768.rs`, lines 28:0-30:1 -/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

/-- **Spec theorem for `spqr.incremental_mlkem768.ek_matches_header`**:

• Takes two `Vec U8` arguments: `ek` (the encapsulation key) and `hdr` (the header).
• Dereferences both to slices, then calls
    `libcrux_ml_kem.mlkem768.incremental.validate_pk_bytes hdr.deref ek.deref`
  which returns a `core.result.Result Unit Error` wrapped in the monadic `Result`.
• Applies `core.result.Result.is_ok` to that inner result, yielding `true` when validation
  succeeds and `false` when it fails.

The postcondition is an exact characterisation, following libcrux 0.0.7
`validate_pk_bytes` / `validate_pk_parts` (`src/ind_cca/incremental.rs` lines 297–339):

  `result = true` **iff**
  - `hdr.len() = 64` and `ek.len() = 1152` (exact lengths; shorter *and* longer inputs are
    rejected with `InvalidInputLength`), and
  - the header hash matches: `H(ek ‖ hdr[0..32]) = hdr[32..64]`
    (`Fips203.Refinement.pk1HashValid hdr.val ek.val`; failure is `InvalidPublicKey`), and
  - the FIPS 203 § 7.2 modulus check passes (`Fips203.Refinement.pk2Valid ek.val`;
    failure is `InvalidPublicKey`).

**Source**: `src/incremental_mlkem768.rs`, lines 28:0-30:1 -/
@[step]
theorem ek_matches_header_spec (ek hdr : alloc.vec.Vec Std.U8) :
    ek_matches_header ek hdr ⦃ (result : Bool) =>
      result = true ↔
        (hdr.length = 64 ∧ ek.length = 1152 ∧
          Fips203.Refinement.pk1HashValid hdr.val ek.val ∧
          Fips203.Refinement.pk2Valid ek.val) ⦄ := by
  unfold ek_matches_header
  simp only [alloc.vec.Vec.deref]
  unfold libcrux_ml_kem.mlkem768.incremental.validate_pk_bytes
  simp only [core.result.Result.is_ok]
  simp only [Slice.from_val, Slice.length, alloc.vec.Vec.length]
  split_ifs with h
  · simp only [bind_ok, WP.spec_ok, Bool.false_eq_true, false_iff, not_and]
    intro h1 h2
    rcases h with h | h
    · exact absurd h1 h
    · exact absurd h2 h
  all_goals simp_all [WP.spec_ok]

/-- On a generated key pair, `ek_matches_header` accepts `(ek, hdr) = (pk2, pk1)`. -/
theorem ek_matches_header_generated (seed : Fin 64 → UInt8)
    (ek hdr : alloc.vec.Vec Std.U8)
    (hek : ek.val = Fips203.Refinement.toU8List (Fips203.Refinement.pk2Bytes seed))
    (hhdr : hdr.val = Fips203.Refinement.toU8List (Fips203.Refinement.pk1Bytes seed)) :
    ek_matches_header ek hdr ⦃ (result : Bool) => result = true ⦄ := by
  unfold ek_matches_header
  simp only [alloc.vec.Vec.deref]
  unfold libcrux_ml_kem.mlkem768.incremental.validate_pk_bytes
  simp only [core.result.Result.is_ok, Slice.from_val, Slice.length, hek, hhdr]
  rw [ite_eq_right (by simp),
    ite_eq_right (not_not.mpr (Fips203.Refinement.pk1HashValid_pk1Bytes seed)),
    ite_eq_right (not_not.mpr (Fips203.Refinement.pk2Valid_pk2Bytes seed))]
  simp [WP.spec_ok]

end spqr.incremental_mlkem768
