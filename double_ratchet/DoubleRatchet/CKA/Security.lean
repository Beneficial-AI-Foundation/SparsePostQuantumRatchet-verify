/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DoubleRatchet.CKA.SecurityGame

/-!
# CKA Security Definition

Definition 13 from Alwen-Coretti-Dodis (2020):
A CKA scheme is `(t, Δ, ε)`-secure if for all `t`-attackers `A`,
`Adv^CKA_{ror,Δ}(A) ≤ ε`.

In the concrete (non-asymptotic) formulation used here, we quantify over
all adversaries without an explicit time bound `t`.
-/

set_option autoImplicit false

namespace CKA

variable {SharedKey SenderState ReceiverState Msg Output : Type}

/-- A CKA scheme is `ε`-secure if every adversary has distinguishing
advantage at most `ε`. This is the concrete version of Definition 13. -/
def CKASecure [SampleableType SharedKey] [SampleableType Output]
    (cka : CKAScheme SharedKey SenderState ReceiverState Msg Output)
    (ε : ℝ) : Prop :=
  ∀ adversary : CKAAdversary Msg Output,
    ckaDistAdvantage cka adversary ≤ ε

end CKA
