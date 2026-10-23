/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Authenticator.Authenticator.VerifyHdr
import Spqr.Auxiliary.Aeneas.Vec
/-!
# Spec theorem for `spqr::v1::unchunked::send_ct::{NoHeaderReceived}::recv_header`

First transition on the ciphertext-sending (B→A) side of the unchunked V1 ratchet.  From the
initial state `{epoch, auth}`, B receives the 64-byte ML-KEM-768 header `hdr` for epoch `epoch`
and a 32-byte tag `mac`.  The function asserts `epoch == self.epoch`, runs
`self.auth.verify_hdr(self.epoch, &hdr, mac)?` (recomputing `mac_hdr` and comparing with `mac`),
and on success returns `HeaderReceived {epoch, auth, hdr}`; on failure `?` maps the
`authenticator::Error` to `Err(Error::MacVerifyFailed)`.

The hax contract is
`requires(epoch == self.epoch && hdr.len() == 64 && mac.len() == Authenticator::MACSIZE)`;
the spec assumes exactly these plus the `mac_key` boundedness hypothesis from `verify_hdr_spec`,
and characterises the `Ok`/`Err` outcome exactly.

**Source**: spqr/src/v1/unchunked/send_ct.rs (lines 100:4-113:5) -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

/- Helper definitions live in a CamelCase namespace so that their full names satisfy the
`defsWithUnderscore` linter; the spec theorems themselves stay in the Rust-mirroring
`spqr.v1.unchunked.send_ct.NoHeaderReceived` namespace. -/
namespace Spqr.V1.Unchunked.SendCt.NoHeaderReceived

/-- Exact condition under which `recv_header` accepts `hdr` with tag `mac`: the recomputed
`mac_hdr self.auth self.epoch hdr` equals the received `mac` (cf. `verify_hdr_spec`). -/
def hdrAccepted (self : spqr.v1.unchunked.send_ct.NoHeaderReceived)
    (hdr mac : alloc.vec.Vec U8) : Prop :=
  spqr.authenticator.Authenticator.mac_hdr self.auth self.epoch hdr.deref = ok mac

/-- Postcondition of `recv_header`: `Ok st` iff `hdrAccepted self hdr mac`, with `st` carrying
`epoch`/`auth` from `self` and storing `hdr`; otherwise `Err MacVerifyFailed`. -/
def recvHeaderPost (self : spqr.v1.unchunked.send_ct.NoHeaderReceived)
    (hdr mac : alloc.vec.Vec U8)
    (result : core.result.Result spqr.v1.unchunked.send_ct.HeaderReceived spqr.Error) : Prop :=
  match result with
  | core.result.Result.Ok st =>
      hdrAccepted self hdr mac ∧
      st.epoch = self.epoch ∧ st.auth = self.auth ∧ st.hdr = hdr
  | core.result.Result.Err e =>
      ¬ hdrAccepted self hdr mac ∧ e = spqr.Error.MacVerifyFailed

end Spqr.V1.Unchunked.SendCt.NoHeaderReceived

namespace spqr.v1.unchunked.send_ct.NoHeaderReceived

open Spqr.V1.Unchunked.SendCt.NoHeaderReceived

/-- **Spec theorem for `spqr.v1.unchunked.send_ct.NoHeaderReceived.recv_header`**:

• Checks `massert (epoch = self.epoch)` (discharged by `h_epoch`), then calls
  `verify_hdr self.auth self.epoch hdr.deref mac.deref`, whose result `r` satisfies
  `r = Ok () ↔ mac_hdr self.auth self.epoch hdr.deref = ok mac` by `verify_hdr_spec`.
• `?` on `r`: `Ok ()` yields `Ok { epoch := self.epoch, auth := self.auth, hdr }`; `Err _`
  yields `Err Error.MacVerifyFailed` (via `Error.Insts.CoreConvertFromError.from`).
• Requires the hax precondition `h_epoch`, `h_hdr`, `h_mac` and the boundedness hypothesis
  `h_key` needed by `verify_hdr_spec`; the call never panics and the branch is decided by
  `hdrAccepted self hdr mac`.

The result satisfies `recvHeaderPost self hdr mac result`.  The proof unfolds `recv_header`,
lets `step*` discharge the assertion and apply `verify_hdr_spec`, then closes both `?` arms by
case analysis on `r`. -/
@[step]
theorem recv_header_spec (self : NoHeaderReceived) (epoch : U64) (hdr mac : alloc.vec.Vec U8)
    (h_epoch : epoch = self.epoch)
    (h_hdr : hdr.length = 64)
    (h_mac : mac.length = authenticator.Authenticator.MACSIZE.val)
    (h_key : self.auth.mac_key.length ≤ U32.max) :
    recv_header self epoch hdr mac ⦃ (result : core.result.Result HeaderReceived Error) =>
      recvHeaderPost self hdr mac result ⦄ := by
  unfold recv_header
  have h_mac_vec : ({ slice := mac.deref } : alloc.vec.Vec U8) = mac :=
    alloc.vec.Vec.ext _ _ (alloc.vec.Vec.deref_val mac)
  step*
  · -- `Ok` arm of `?`: `verify_hdr` accepted, so `mac_hdr … = ok mac`.
    refine ⟨?_, rfl, rfl, rfl⟩
    rcases r with _ | e
    · simpa [hdrAccepted, h_mac_vec] using r_post.mp rfl
    · simp at cf_post; simp [cf_post] at *
  · -- `Err` arm of `?`: `verify_hdr` rejected, the error is mapped to `MacVerifyFailed`.
    subst result_post1
    simp only [Error.Insts.CoreConvertFromError.from, ok.injEq] at result_post
    subst result_post
    refine ⟨fun h => ?_, rfl⟩
    rcases r with _ | e'
    · simp at cf_post; simp [cf_post] at *
    · have := r_post.mpr (by simpa [hdrAccepted, h_mac_vec] using h)
      simp at this

/-- **Spec theorem for `spqr.v1.unchunked.send_ct.NoHeaderReceived.recv_header`** (accepting
case): under `hdrAccepted self hdr mac` the call returns `Ok { self.epoch, self.auth, hdr }`.
Projection of `recv_header_spec`. -/
theorem recv_header_spec_ok (self : NoHeaderReceived) (epoch : U64) (hdr mac : alloc.vec.Vec U8)
    (h_epoch : epoch = self.epoch)
    (h_hdr : hdr.length = 64)
    (h_mac : mac.length = authenticator.Authenticator.MACSIZE.val)
    (h_key : self.auth.mac_key.length ≤ U32.max)
    (h_acc : hdrAccepted self hdr mac) :
    recv_header self epoch hdr mac ⦃ (result : core.result.Result HeaderReceived Error) =>
      result = core.result.Result.Ok { epoch := self.epoch, auth := self.auth, hdr } ⦄ := by
  apply WP.spec_mono (recv_header_spec self epoch hdr mac h_epoch h_hdr h_mac h_key)
  intro result h
  cases result with
  | Ok st =>
    obtain ⟨_, h1, h2, h3⟩ := h
    cases st
    simp_all
  | Err e => exact absurd h_acc h.1

/-- **Spec theorem for `spqr.v1.unchunked.send_ct.NoHeaderReceived.recv_header`** (rejecting
case): under `¬ hdrAccepted self hdr mac` the call returns `Err Error.MacVerifyFailed`.
Projection of `recv_header_spec`. -/
theorem recv_header_spec_err (self : NoHeaderReceived) (epoch : U64) (hdr mac : alloc.vec.Vec U8)
    (h_epoch : epoch = self.epoch)
    (h_hdr : hdr.length = 64)
    (h_mac : mac.length = authenticator.Authenticator.MACSIZE.val)
    (h_key : self.auth.mac_key.length ≤ U32.max)
    (h_rej : ¬ hdrAccepted self hdr mac) :
    recv_header self epoch hdr mac ⦃ (result : core.result.Result HeaderReceived Error) =>
      result = core.result.Result.Err Error.MacVerifyFailed ⦄ := by
  apply WP.spec_mono (recv_header_spec self epoch hdr mac h_epoch h_hdr h_mac h_key)
  intro result h
  cases result with
  | Ok st => exact absurd h.1 h_rej
  | Err e => rw [h.2]

end spqr.v1.unchunked.send_ct.NoHeaderReceived
