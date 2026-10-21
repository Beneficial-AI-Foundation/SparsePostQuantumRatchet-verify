/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.V1.Unchunked.SendCt.Serialize.NoHeaderReceived.New
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.NewWithPolyCount
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.New
import Spqr.Specs.Authenticator.Authenticator.MACSIZE
import Spqr.Specs.IncrementalMlkem768.HEADER_SIZE
import Spqr.Specs.Aeneas.ResultExpect
/-!
# Spec theorem for `spqr::v1::chunked::send_ct::{NoHeaderReceived}::new`

`NoHeaderReceived::new` builds the very first state of the ciphertext-sending (B→A) side of the
*chunked* V1 ratchet.  It wraps the unchunked state of the same name and adds the erasure-coding
machinery needed to reassemble A's header out of fixed-size chunks:

  1. `uc` — the unchunked `NoHeaderReceived` (epoch `1` plus a fresh `Authenticator` derived
     from `auth_key`), obtained by `unchunked::NoHeaderReceived::new(auth_key)`;
  2. `receiving_hdr` — a `PolyDecoder` sized for the incoming header, i.e. for
     `HEADER_SIZE + MACSIZE = 64 + 32 = 96` bytes.

`PolyDecoder::new(len)` only fails when `len` is odd (`Err MessageLengthEven`), since every
GF(2¹⁶) point packs two bytes.  Because `96` is even, the `Result` is always `Ok` and the
`.expect("should be able to decode header size")` in the Rust source can never panic; the
resulting decoder needs `96 / 2 = 48` points, starts with all `16` polynomials empty, and is
not yet complete.

`HEADER_SIZE` is defined in the Rust source as `libcrux_ml_kem::mlkem768::incremental::pk1_len()`
(`= 64`, the size of `ρ ‖ H(ek)`); its value is provided by `HEADER_SIZE_spec`.

The only way the construction can fail is if `auth_key` prefixed by the 32-byte zero
root key cannot fit in memory, hence the precondition `auth_key.length + 32 ≤ Usize.max`
inherited from the unchunked constructor.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 71:4-79:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr.v1.chunked.send_ct.NoHeaderReceived

open List core.num.U64 authenticator.Authenticator in
/-- **Spec theorem for `spqr.v1.chunked.send_ct.NoHeaderReceived.new`**:

• Takes a byte slice `auth_key` (the shared authentication key agreed by both parties).
• Computes `i1 = HEADER_SIZE + MACSIZE = 64 + 32 = 96` (no overflow: both are small constants).
• Calls `PolyDecoder.Insts.SpqrEncodingDecoder.new 96`, which returns
    `Ok { pts_needed := 48, pts := replicate 16 ∅, is_complete := false }`
  because `96` is even.
• Delegates to `unchunked.send_ct.NoHeaderReceived.new auth_key` for the inner state `nhr`.
• Unwraps the decoder with `Result.expect`, which succeeds on `Ok`.
• Returns `{ uc := nhr, receiving_hdr := pd }`.

• Requires that `auth_key` prefixed by the 32 zero bytes of the empty initial authenticator
  state fits in memory: `auth_key.length + 32 ≤ Usize.max`.  Under this hypothesis the call
  always succeeds (no panic).

The result satisfies the postcondition:

  `result.uc.epoch = 1`
  `result.uc.auth.root_key.length = 32`
  `result.uc.auth.mac_key.length = 32`
  `result.uc.auth.root_key.val ++ result.uc.auth.mac_key.val =
       hkdf (replicate 32 0#u8) (replicate 32 0#u8 ++ auth_key.val)
         (updateLabel ++ to_be_bytes 1#u64) 64`
  `result.receiving_hdr.pts_needed.val = 48`
  `result.receiving_hdr.pts.val = replicate 16 default`
  `result.receiving_hdr.is_complete = false`

The proof unfolds `new` and runs `step*` (using the registered `HEADER_SIZE_spec` and the
`new_spec`s for the decoder and the unchunked state).  The `HEADER_SIZE + MACSIZE` overflow
side goal is closed with `MACSIZE_spec` and `scalar_tac`.  Knowing `i1 = 96` is even, the
decoder's postcondition reduces to its `Ok` branch; case analysis on the `PolyDecoder::new`
result rules out `Err`, `expect_ok_spec` unwraps the decoder, and the conjuncts are assembled
from the collected postconditions (`pts_needed = 96 / 2 = 48` by `rfl`).

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 71:4-79:5)
-/
@[step]
theorem new_spec (auth_key : Slice U8)
    (h : auth_key.length + 32 ≤ Usize.max) :
    new auth_key ⦃ (result : NoHeaderReceived) =>
      result.uc.epoch = 1#u64 ∧
      result.uc.auth.root_key.length = 32 ∧
      result.uc.auth.mac_key.length = 32 ∧
      result.uc.auth.root_key.val ++ result.uc.auth.mac_key.val
        = hkdf (replicate 32 0#u8) (replicate 32 0#u8 ++ auth_key.val)
          (updateLabel ++ to_be_bytes 1#u64) 64 ∧
      result.receiving_hdr.pts_needed.val = 48 ∧
      result.receiving_hdr.pts.val = replicate 16 default ∧
      result.receiving_hdr.is_complete = false ⦄ := by
  unfold new
  step*
  · have hi : i.val = 64 := «Spqr.Mlkem.headerBytes_post»
    simp only [hi, authenticator.Authenticator.MACSIZE_spec]; scalar_tac
  · have h_i1 : i1.val = 96 := by
      have hi : i.val = 64 := «Spqr.Mlkem.headerBytes_post»
      simp only [i1_post, hi, authenticator.Authenticator.MACSIZE_spec]
    simp only [h_i1, Nat.reduceMod, ↓reduceIte] at decoder_post
    cases decoder with
    | Err e => exact absurd decoder_post not_false
    | Ok pd0 =>
      step*
      subst pd_post
      obtain ⟨h_pts, h_vec, h_done⟩ := decoder_post
      refine ⟨nhr_post, nhr_post1, nhr_post2, nhr_post3, ?_, h_vec, h_done⟩
      rw [h_pts]; rfl

end spqr.v1.chunked.send_ct.NoHeaderReceived
