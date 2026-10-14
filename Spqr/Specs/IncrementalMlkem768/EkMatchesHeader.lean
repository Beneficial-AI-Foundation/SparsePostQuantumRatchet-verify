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

The postcondition gives exact conditions:

  - `result = false` when `hdr` is too short (length < 64),
  - `result = false` when `ek` is too short (length < 1152),
  - `result = true`  when both lengths are sufficient and `pk2Valid ek.val` holds,
  - `result = false` when both lengths are sufficient but `pk2Valid ek.val` fails.

**Source**: `src/incremental_mlkem768.rs`, lines 28:0-30:1 -/
@[step]
theorem ek_matches_header_spec (ek hdr : alloc.vec.Vec Std.U8) :
    ek_matches_header ek hdr ⦃ (result : Bool) =>
      let hdrSlice := alloc.vec.Vec.deref hdr
      let ekSlice := alloc.vec.Vec.deref ek
      (hdrSlice.length < 64 → result = false) ∧
      (64 ≤ hdrSlice.length → ekSlice.length < 1152 → result = false) ∧
      (64 ≤ hdrSlice.length → 1152 ≤ ekSlice.length →
        Fips203.Bridge.pk2Valid ekSlice.val → result = true) ∧
      (64 ≤ hdrSlice.length → 1152 ≤ ekSlice.length →
        ¬ Fips203.Bridge.pk2Valid ekSlice.val → result = false) ⦄ := by
  unfold ek_matches_header
  simp only [alloc.vec.Vec.deref]
  unfold libcrux_ml_kem.mlkem768.incremental.validate_pk_bytes
  simp only [core.result.Result.is_ok]
  split_ifs <;> simp_all [WP.spec_ok]

end spqr.incremental_mlkem768
