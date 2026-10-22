/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.IncrementalMlkem768.Encaps2
public import Spqr.Specs.Authenticator.Authenticator.MacCt
import Spqr.Specs.Aeneas.VecExtendFromSlice
import Spqr.Auxiliary.Aeneas.Vec
/-!
# Spec theorem for `spqr::v1::unchunked::send_ct::{Ct1SentEkReceived}::send_ct2`

Completes encapsulation and authenticates the ciphertext. From `Ct1SentEkReceived`
`{epoch, auth, es, ek, ct1}`: runs `encaps2(ek, es)` → 128-byte `ct2`, concatenates
`ct1 ‖ ct2` into the full 1088-byte ciphertext, computes `mac = auth.mac_ct(epoch, ct1‖ct2)`,
and returns `(Ct2Sent {epoch, auth}, ct2, mac)`.

Strengthens the hax `ensures` (`ct2.len() == 128 ∧ mac.len() == MACSIZE`) to full FIPS 203 /
HMAC value semantics via `encaps2_spec`, `extend_from_slice_U8_spec`, and `mac_ct_spec`.

**Source**: spqr/src/v1/unchunked/send_ct.rs (lines 177:4-195:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr Spqr.IncrementalMlkem768

namespace spqr.v1.unchunked.send_ct.Ct1SentEkReceived

open List core.num.U64 authenticator.Authenticator in
/-- **Spec theorem for `spqr.v1.unchunked.send_ct.Ct1SentEkReceived.send_ct2`**:

Requires `ek.len() = 1152`, `es.len() = 2080`, `mac_key.len() ≤ U32.max`, and
`ct1.len() + 128 + 43 ≤ U32.max`. Returns `(st, ct2, mac)` where:
- `st.epoch = self.epoch ∧ st.auth = self.auth`
- `ct2.len() = 128 ∧ Encaps2Post self.ek self.es ct2` (FIPS 203 round 2)
- `mac.len() = MACSIZE` and equals `HMAC-SHA256(mac_key, MAC_CT_LABEL ‖ epoch ‖ ct1 ‖ ct2)`
  over the *complete* ciphertext, binding both halves to the same epoch. -/
@[step]
theorem send_ct2_spec (self : Ct1SentEkReceived)
    (h_ek : self.ek.length = 1152)
    (h_es : self.es.length = 2080)
    (h_key : self.auth.mac_key.length ≤ U32.max)
    (h_ct : self.ct1.length + 128 + 43 ≤ U32.max) :
    send_ct2 self ⦃
      (result : Ct2Sent × (alloc.vec.Vec U8) × (alloc.vec.Vec U8)) =>
      let st := result.1
      let ct2 := result.2.1
      let mac := result.2.2
      st.epoch = self.epoch ∧ st.auth = self.auth ∧
      ct2.length = 128 ∧ Encaps2Post self.ek self.es ct2 ∧
      mac.length = MACSIZE.val ∧
      ∃ data : Slice U8,
        data.val = MAC_CT_LABEL ++ to_be_bytes self.epoch ++ (self.ct1.val ++ ct2.val) ∧
        libcrux_hmac.hmac .Sha256 self.auth.mac_key.deref data (some MACSIZE) = ok mac ⦄ := by
  unfold send_ct2
  step with incremental_mlkem768.encaps2_spec self.ek self.es h_ek h_es
    as ⟨ct2, h_ct2_post, h_ct2_len⟩
  step*
  · scalar_tac
  · refine ⟨h_ct2_len, h_ct2_post, mac_post, _, ?_,
      ‹libcrux_hmac.hmac .Sha256 _ _ _ = ok _›⟩
    simp only [Slice.from_val, alloc.vec.Vec.deref_val, ct1_post]

end spqr.v1.unchunked.send_ct.Ct1SentEkReceived
