/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.IncrementalMlkem768.EkMatchesHeader
/-!
# Spec theorem for `spqr::v1::unchunked::send_ct::{Ct1Sent}::recv_ek`

After sending `ct1` against the peer's header `hdr = ρ ‖ H(ek)`, B receives the full
ML-KEM-768 encapsulation key `ek` and checks it against the header. Given state
`{epoch, auth, hdr, es, ct1}` the function:

  1. asserts `epoch == self.epoch`;
  2. runs `ek_matches_header(&ek, &self.hdr)`, true iff `hdr.len() == 64`, `ek.len() == 1152`,
     `H(ek ‖ hdr[0..32]) = hdr[32..64]` and `ek` passes the FIPS 203 § 7.2 modulus check;
  3. on success returns `Ct1SentEkReceived {epoch, auth, ek, es, ct1}` (dropping `hdr`);
  4. on failure returns `Err(Error::ErroneousDataReceived)`.

The hax contract is `requires(epoch == self.epoch && ek.len() == 1152)`; only the first
conjunct is needed for panic-freedom, so the spec assumes just `epoch = self.epoch` and
characterises the `Ok`/`Err` outcome exactly.

**Source**: spqr/src/v1/unchunked/send_ct.rs (lines 154:4-171:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

/- Helper definitions live in a CamelCase namespace so that their full names satisfy the
`defsWithUnderscore` linter; the spec theorem itself stays in the Rust-mirroring
`spqr.v1.unchunked.send_ct.Ct1Sent` namespace. -/
namespace Spqr.V1.Unchunked.SendCt.Ct1Sent

/-- Condition under which `recv_ek` accepts `ek`, i.e. `ek_matches_header ek self.hdr = true`
(see `ek_matches_header_spec`): `hdr` has 64 bytes, `ek` has 1152 bytes,
`H(ek ‖ hdr[0..32]) = hdr[32..64]` (`pk1HashValid`) and `ek` passes the FIPS 203 § 7.2
modulus check (`pk2Valid`). -/
def ekAccepted (self : spqr.v1.unchunked.send_ct.Ct1Sent) (ek : alloc.vec.Vec U8) : Prop :=
  self.hdr.length = 64 ∧ ek.length = 1152 ∧
    Fips203.Refinement.pk1HashValid self.hdr.val ek.val ∧
    Fips203.Refinement.pk2Valid ek.val

/-- Postcondition of `recv_ek`: `Ok st` iff `ekAccepted self ek`, with `st` carrying `epoch`,
`auth`, `es`, `ct1` over unchanged and storing `ek`; otherwise `Err ErroneousDataReceived`. -/
def recvEkPost (self : spqr.v1.unchunked.send_ct.Ct1Sent) (ek : alloc.vec.Vec U8)
    (result : core.result.Result spqr.v1.unchunked.send_ct.Ct1SentEkReceived spqr.Error) : Prop :=
  match result with
  | core.result.Result.Ok st =>
      ekAccepted self ek ∧
      st.epoch = self.epoch ∧ st.auth = self.auth ∧ st.es = self.es ∧
      st.ek = ek ∧ st.ct1 = self.ct1
  | core.result.Result.Err e =>
      ¬ ekAccepted self ek ∧ e = spqr.Error.ErroneousDataReceived

end Spqr.V1.Unchunked.SendCt.Ct1Sent

namespace spqr.v1.unchunked.send_ct.Ct1Sent

open Spqr.V1.Unchunked.SendCt.Ct1Sent

/-- **Spec theorem for `spqr.v1.unchunked.send_ct.Ct1Sent.recv_ek`**:

• Asserts `epoch = self.epoch` (discharged by `h_epoch`).
• Calls `ek_matches_header ek self.hdr`, giving `b` with `b = true ↔ ekAccepted self ek`
  (`ek_matches_header_spec`).
• Returns `Ok { epoch := self.epoch, auth := self.auth, es := self.es, ek, ct1 := self.ct1 }`
  if `b`, else `Err Error.ErroneousDataReceived`.

Requires only `h_epoch : epoch = self.epoch`; the call never panics and the result satisfies
`recvEkPost self ek result`.

Proof: unfold, `step*` handles the assertion and the `ek_matches_header` call, then the `Ok`
branch follows from `b_post.mp` plus `rfl`, the `Err` branch from its contrapositive.

**Source**: spqr/src/v1/unchunked/send_ct.rs (lines 154:4-171:5)
-/
@[step]
theorem recv_ek_spec (self : Ct1Sent) (epoch : U64) (ek : alloc.vec.Vec U8)
    (h_epoch : epoch = self.epoch) :
    recv_ek self epoch ek ⦃ (result : core.result.Result Ct1SentEkReceived Error) =>
      recvEkPost self ek result ⦄ := by
  unfold recv_ek
  step*
  · exact ⟨b_post.mp (by assumption), rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨fun h => by simp_all [ekAccepted], rfl⟩

/-- **Spec theorem for `spqr.v1.unchunked.send_ct.Ct1Sent.recv_ek`** (accepting case):

Under `ekAccepted self ek` the call returns `Ok` with all fields fixed. Projection of
`recv_ek_spec`.

**Source**: spqr/src/v1/unchunked/send_ct.rs (lines 154:4-171:5)
-/
theorem recv_ek_spec_ok (self : Ct1Sent) (epoch : U64) (ek : alloc.vec.Vec U8)
    (h_epoch : epoch = self.epoch)
    (h_acc : ekAccepted self ek) :
    recv_ek self epoch ek ⦃ (result : core.result.Result Ct1SentEkReceived Error) =>
      result = core.result.Result.Ok
        { epoch := self.epoch, auth := self.auth, es := self.es, ek, ct1 := self.ct1 } ⦄ := by
  apply WP.spec_mono (recv_ek_spec self epoch ek h_epoch)
  intro result h
  cases result with
  | Ok st =>
    obtain ⟨_, h1, h2, h3, h4, h5⟩ := h
    cases st
    simp_all
  | Err e => exact absurd h_acc h.1

/-- **Spec theorem for `spqr.v1.unchunked.send_ct.Ct1Sent.recv_ek`** (rejecting case):

Under `¬ ekAccepted self ek` the call returns `Err Error.ErroneousDataReceived`.
Projection of `recv_ek_spec`.

**Source**: spqr/src/v1/unchunked/send_ct.rs (lines 154:4-171:5)
-/
theorem recv_ek_spec_err (self : Ct1Sent) (epoch : U64) (ek : alloc.vec.Vec U8)
    (h_epoch : epoch = self.epoch)
    (h_rej : ¬ ekAccepted self ek) :
    recv_ek self epoch ek ⦃ (result : core.result.Result Ct1SentEkReceived Error) =>
      result = core.result.Result.Err Error.ErroneousDataReceived ⦄ := by
  apply WP.spec_mono (recv_ek_spec self epoch ek h_epoch)
  intro result h
  cases result with
  | Ok st => exact absurd h.1 h_rej
  | Err e => rw [h.2]

end spqr.v1.unchunked.send_ct.Ct1Sent
