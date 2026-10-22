/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.IncrementalMlkem768.Generate
public import Spqr.Specs.Authenticator.Authenticator.MacHdr
import Spqr.Auxiliary.Aeneas.SpecRefl
import Spqr.Auxiliary.Aeneas.Vec
/-!
# Spec theorem for `spqr::v1::unchunked::send_ek::{KeysUnsampled}::send_header`

From a `KeysUnsampled` state (epoch + authenticator), this function:
1. samples an incremental ML-KEM-768 key pair → `hdr` (64 B), `ek` (1152 B), `dk` (2400 B);
2. MACs the header via `mac_hdr(epoch, hdr)` → 32-byte HMAC-SHA256 tag;
3. transitions to `HeaderSent`, preserving `epoch`/`auth` and storing `ek`/`dk`.

The caller sends `(hdr, mac)` to B for `verify_hdr`. The spec theorem strengthens the Rust
`ensures` with FIPS 203 key-pair semantics and the defining HMAC equation. The RNG is
threaded explicitly after Aeneas extraction.

**Source**: spqr/src/v1/unchunked/send_ek.rs (lines 84:4-100:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.v1.unchunked.send_ek.KeysUnsampled

/-- `mac_hdr_spec` strengthened with `… = ok r`; registered locally as `step` so
the postcondition exposes the form consumed by `verify_hdr_spec`. -/
private theorem mac_hdr_spec_refl :
    type_of% (refl_of% authenticator.Authenticator.mac_hdr_spec) :=
  refl_of% authenticator.Authenticator.mac_hdr_spec

attribute [local step] mac_hdr_spec_refl
attribute [-step] authenticator.Authenticator.mac_hdr_spec

-- Register `generate_spec` locally so `step*` can discharge the `generate` call.
attribute [local step] incremental_mlkem768.generate_spec

open List core.num.U64 authenticator.Authenticator
  libcrux_ml_kem.mlkem768.incremental Spqr.Mlkem in
/-- **Spec theorem for `spqr.v1.unchunked.send_ek.KeysUnsampled.send_header`**:

Given `self : KeysUnsampled` and RNG `rng`, generates an ML-KEM-768 key pair, MACs the header,
and returns `(HeaderSent, hdr, mac, rng1)`. Postcondition preserves `epoch`/`auth`, asserts
correct lengths (hdr=64, mac=32, ek=1152, dk=2400), FIPS 203 seed semantics, slice relations,
and the `mac_hdr … = ok mac` equation needed by `verify_hdr_spec`.

Requires panic-free `fill_bytes` (`h_fill`) and `mac_key.length ≤ U32.max` (`h_key`).
The `hdr.length + 41 ≤ U32.max` side condition is discharged automatically.

Proof: unfold + `step*`, then `scalar_tac` for the MAC side condition and `Slice.ext` for
the final HMAC equation.

**Source**: spqr/src/v1/unchunked/send_ek.rs (lines 84:4-100:5)
-/
@[step]
theorem send_header_spec {R : Type} (rngInst : rand_1.rng.Rng R)
    (cryptoInst : rand_core_1.CryptoRng R) (self : KeysUnsampled) (rng : R)
    (h_fill : ∀ (r : R) (s : Slice U8),
      rngInst.rand_core_1RngCoreInst.fill_bytes r s ⦃ fun _ => True ⦄)
      (h_key : self.auth.mac_key.length ≤ U32.max) :
    send_header rngInst cryptoInst self rng ⦃
      (result : (HeaderSent × alloc.vec.Vec U8 × alloc.vec.Vec U8) × R) =>
      let state := result.1.1
      let hdr := result.1.2.1
      let mac := result.1.2.2
      state.epoch = self.epoch ∧
      state.auth = self.auth ∧
      hdr.length = headerBytes ∧
      mac.length = MACSIZE.val ∧
      state.ek.length = mlkem768Params.encapsulationKeyBytes ∧
      state.dk.length = mlkem768Params.decapsulationKeyBytes ∧
      (∃ seed : Fin 64 → UInt8,
        state.dk.val = Fips203.Refinement.keyPairList seed ∧
        state.ek.val = Fips203.Refinement.toU8List (Fips203.Refinement.pk2Bytes seed) ∧
        hdr.val = Fips203.Refinement.toU8List (Fips203.Refinement.pk1Bytes seed)) ∧
      state.ek.val = state.dk.val.slice mlkem768Params.encapsulationKeyBytes
        (2 * mlkem768Params.encapsulationKeyBytes) ∧
      hdr.val = state.dk.val.slice (2 * mlkem768Params.encapsulationKeyBytes)
        (2 * mlkem768Params.encapsulationKeyBytes + headerBytes) ∧
      mac_hdr self.auth self.epoch hdr.deref = ok mac ∧
      ∀ data : Slice U8, data.val = MAC_HDR_LABEL ++ to_be_bytes self.epoch ++ hdr.val →
        libcrux_hmac.hmac .Sha256 self.auth.mac_key.deref data (some MACSIZE) = ok mac ⦄ := by
  unfold send_header
  step*
  · have hhdr : headerBytes = 64 := by decide
    have : (keys.hdr.deref).length = 64 := by
      rw [alloc.vec.Vec.deref_length, ‹keys.hdr.length = headerBytes›, hhdr]
    simp_all only [alloc.vec.Vec.length, Fips203.Refinement.toU8List_length, ReduceNat.reduceNatEq,
      Slice.length, alloc.vec.Vec.deref_val, Nat.reduceAdd, ge_iff_le, Nat.reduceMul]
    scalar_tac
  · and_intros
    all_goals try (first | rfl | assumption | exact ⟨seed, keys_post, keys_post1, keys_post2⟩)
    intro data h_data
    convert mac_post1
    apply Slice.ext; simp [h_data]

end spqr.v1.unchunked.send_ek.KeysUnsampled
