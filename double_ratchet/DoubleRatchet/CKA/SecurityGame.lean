/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DoubleRatchet.CKA.Defs
import VCVio.EvalDist.Bool
import VCVio.OracleComp.Constructions.SampleableType

/-!
# CKA Security Game

Single-epoch real-or-random security game for CKA, corresponding to Figure 3
from Alwen-Coretti-Dodis (2020).

For Theorem 3 (DDH → CKA security with Δ=1), the single-epoch game suffices:
the DDH reduction is a single-step embedding. The full multi-epoch game with
corruption oracles (needed for the composition Theorem 6) is left as a future
extension.
-/

set_option autoImplicit false

open OracleComp ENNReal

namespace CKA

/-- A single-epoch CKA adversary receives a public message and a candidate
output key, and guesses whether the key is real or random. -/
def CKAAdversary (Msg Output : Type) := Msg → Output → ProbComp Bool

section Games

variable {SharedKey SenderState ReceiverState Msg Output : Type}

variable [SampleableType SharedKey]

/-- CKA real game: the adversary sees the genuine output key.
Sample a shared key, initialize, send, and give the adversary the real output. -/
def ckaRealExp
    (cka : CKAScheme SharedKey SenderState ReceiverState Msg Output)
    (adversary : CKAAdversary Msg Output) : ProbComp Bool := do
  let k ← $ᵗ SharedKey
  let (sndSt, _rcvSt) ← cka.init k
  let (_sndSt', msg, output) ← cka.send sndSt
  adversary msg output

variable [SampleableType Output]

/-- CKA random game: the adversary sees a uniformly random output key.
Same as the real game but the output key is replaced with a fresh random sample. -/
def ckaRandExp
    (cka : CKAScheme SharedKey SenderState ReceiverState Msg Output)
    (adversary : CKAAdversary Msg Output) : ProbComp Bool := do
  let k ← $ᵗ SharedKey
  let (sndSt, _rcvSt) ← cka.init k
  let (_sndSt', msg, _output) ← cka.send sndSt
  let randOutput ← $ᵗ Output
  adversary msg randOutput

/-- CKA distinguishing advantage: `|Pr[output 1 | real] - Pr[output 1 | random]|`.
Corresponds to `Adv^CKA_{ror,Δ}(A)` from Definition 13 in ACD 2020. -/
noncomputable def ckaDistAdvantage
    (cka : CKAScheme SharedKey SenderState ReceiverState Msg Output)
    (adversary : CKAAdversary Msg Output) : ℝ :=
  |(Pr[= true | ckaRealExp cka adversary]).toReal -
    (Pr[= true | ckaRandExp cka adversary]).toReal|

end Games

end CKA
