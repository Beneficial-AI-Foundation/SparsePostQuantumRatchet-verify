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

`NoHeaderReceived::new` builds the initial B→A state of the *chunked* V1 ratchet: the
unchunked `NoHeaderReceived` (`uc`, epoch `1` with a fresh `Authenticator` from `auth_key`)
plus a `PolyDecoder` (`receiving_hdr`) for the `HEADER_SIZE + MACSIZE = 64 + 32 = 96`-byte
header.

`PolyDecoder::new` fails only on odd lengths; `96` is even, so the Rust `.expect` never
panics and the decoder needs `48` points, starts with `16` empty polynomials, and is incomplete.
`HEADER_SIZE = 64` comes from `HEADER_SIZE_spec`.

The precondition `auth_key.length + 32 ≤ Usize.max` is inherited from the unchunked constructor.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 71:4-79:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr.v1.chunked.send_ct.NoHeaderReceived

open List core.num.U64 authenticator.Authenticator in
/-- **Spec theorem for `spqr.v1.chunked.send_ct.NoHeaderReceived.new`**:

• Computes `i1 = HEADER_SIZE + MACSIZE = 96` (no overflow) and calls `PolyDecoder.new 96`,
  which is `Ok` since `96` is even.
• Builds the inner state via `unchunked.send_ct.NoHeaderReceived.new auth_key`, unwraps the
  decoder with `Result.expect`, and returns `{ uc := nhr, receiving_hdr := pd }`.
• Requires `auth_key.length + 32 ≤ Usize.max`; then the call never panics.

Postcondition: `uc.epoch = 1`, both authenticator keys have length `32` and their
concatenation equals the `hkdf` derivation from the zero root key and `auth_key`;
`receiving_hdr` needs `48` points, has `16` default polynomials, and is not complete.

Proof: unfold `new`, `step*`; close the overflow goal with `MACSIZE_spec`/`scalar_tac`;
rewrite `i1 = 96` so the decoder postcondition reduces to the `Ok` branch, rule out `Err`,
unwrap with `expect`, and assemble the conjuncts (`pts_needed = 48` by `rfl`). -/
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
  rw [incremental_mlkem768.HEADER_SIZE_eq, bind_ok]
  step*
  · simp only [authenticator.Authenticator.MACSIZE_spec]; scalar_tac
  · have h_i1 : i1.val = 96 := by
      simp only [i1_post, authenticator.Authenticator.MACSIZE_spec]
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
