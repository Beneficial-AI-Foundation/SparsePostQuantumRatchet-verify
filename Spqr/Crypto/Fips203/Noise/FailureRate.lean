/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Crypto.Fips203.Noise.TailBound
import Spqr.Crypto.Fips203.Noise.Compression
import Spqr.Crypto.Fips203.KEM.RoundTrip
/-!
# Decryption-Failure Events and the Union-Bound Failure Count

Step 8.5 of the probabilistic noise analysis (plan.md, Phase 8).  This file names the
decryption-failure events of ML-KEM and assembles the counting-level union bound:

* `noiseViolation` — the per-coefficient failure event
  `⌊q/4⌋ ≤ |honestW − Decompress₁(m)|` (the negation of the `h_noise` hypothesis of
  `kpke_roundTrip` / `mlkem_roundTrip` at one coefficient);
* `noiseOk` and `noiseOk_iff_not_exists` — the global noise bound and its reformulation as
  "no coefficient violates";
* `mlkem_roundTrip_of_not_violation` — the KEM round trip restated with the failure event:
  decapsulation recovers the shared secret whenever no `noiseViolation` occurs;
* `card_noiseFail_le_sum` — over **any** finite seed space `α` (with seed-dependent
  `d`, `m`, `r`), the number of seeds on which decryption fails is at most the sum over
  the `256` coefficients of the per-coefficient violation counts (union bound of step 8.4);
* `card_noiseFail_le_of_bound` — if each per-coefficient count is `≤ c`, the failure count
  is `≤ 256 · c`, i.e. `P[failure] ≤ 256 · P_max[coeff violation]`.

The seed space is abstract because the randomness of `honestW` flows through the opaque hash
oracles (`hashG`, `prf`, `xof` of `PKE/KeyGen.lean`); a concrete numeric `δ` (FIPS 203 § 3.3:
`δ ≤ 2⁻¹⁶⁴`) requires a uniformity assumption on the oracle outputs, under which the
per-coefficient count is bounded by the CBD tails of `Noise/TailBound.lean` combined with the
compression budget of `Noise/Compression.lean` (`2 + 105 < 832`).  That instantiation is
deliberately left as a hypothesis (`hc`) of `card_noiseFail_le_of_bound`.

**Source**: NIST FIPS 203, § 3.3 (decryption failure rate)
-/

noncomputable section

namespace Fips203

/-! ## Failure events -/

/-- **Per-coefficient noise violation**: coefficient `idx` of the decryption-noise polynomial
reaches the threshold `⌊q/4⌋ = 832`.  This is the negation, at one coefficient, of the
`h_noise` hypothesis of `kpke_roundTrip` / `mlkem_roundTrip`. -/
def noiseViolation (d m r : Fin 32 → UInt8) (p : ParamSet) (idx : Fin n) : Prop :=
  q / 4 ≤ absZq (honestW d m r p idx - decompressMsg m idx)

/-- **Global noise bound**: every coefficient of the noise polynomial is below `⌊q/4⌋`.
This is exactly the `h_noise` hypothesis of `kpke_roundTrip` / `mlkem_roundTrip`. -/
def noiseOk (d m r : Fin 32 → UInt8) (p : ParamSet) : Prop :=
  ∀ idx : Fin n, absZq (honestW d m r p idx - decompressMsg m idx) < q / 4

/-- The global bound holds iff no coefficient violates. -/
theorem noiseOk_iff_not_exists (d m r : Fin 32 → UInt8) (p : ParamSet) :
    noiseOk d m r p ↔ ¬ ∃ idx : Fin n, noiseViolation d m r p idx := by
  unfold noiseOk noiseViolation
  push Not
  rfl

/-- **KEM round trip, failure-event form**: if no coefficient of the noise polynomial at the
derived randomness `honestR d m p` violates the threshold, decapsulating the honestly
encapsulated ciphertext recovers the shared secret. -/
theorem mlkem_roundTrip_of_not_violation (p : ParamSet) (d z m : Fin 32 → UInt8)
    (h : ¬ ∃ idx : Fin n, noiseViolation d m (honestR d m p) p idx) :
    mlkemDecaps p (mlkemKeyGen d z p).dk (mlkemEncaps p (mlkemKeyGen d z p).ek m).ct =
      (mlkemEncaps p (mlkemKeyGen d z p).ek m).ss :=
  mlkem_roundTrip p d z m ((noiseOk_iff_not_exists d m (honestR d m p) p).mpr h)

/-! ## Union-bound failure count over a finite seed space

The randomness of an honest ML-KEM execution is a finite object (the seeds `d`, `m` and the
derived encryption randomness `r`).  We work over an abstract finite type `α` of "random
tapes" with seed projections, so the statements apply both to the full tape (all oracle
outputs) and to restricted experiments. -/

open scoped Classical in
/-- **Union bound on the failure count**: over any finite seed space, the number of seeds on
which some coefficient violates is at most the sum of the per-coefficient violation counts.
Instantiates `card_filter_exists_le` of step 8.4 with `ι = Fin 256`. -/
theorem card_noiseFail_le_sum {α : Type*} [Fintype α]
    (seedD seedM seedR : α → (Fin 32 → UInt8)) (p : ParamSet) :
    (Finset.univ.filter fun a =>
        ∃ idx : Fin n, noiseViolation (seedD a) (seedM a) (seedR a) p idx).card ≤
      ∑ idx : Fin n, (Finset.univ.filter fun a =>
        noiseViolation (seedD a) (seedM a) (seedR a) p idx).card := by
  have h := card_filter_exists_le (α := α) Finset.univ
    (fun idx a => noiseViolation (seedD a) (seedM a) (seedR a) p idx)
  refine le_trans (le_of_eq (congrArg Finset.card
    (Finset.filter_congr fun a _ => ?_))) h
  simp only [Finset.mem_univ, true_and]

open scoped Classical in
/-- **Failure count from a uniform per-coefficient bound**: if every coefficient's violation
count is at most `c`, the failure count is at most `256 · c`.  Dividing by `|α|`:
`P[decryption failure] ≤ 256 · max_idx P[coefficient idx violates]`. -/
theorem card_noiseFail_le_of_bound {α : Type*} [Fintype α]
    (seedD seedM seedR : α → (Fin 32 → UInt8)) (p : ParamSet) (c : ℕ)
    (hc : ∀ idx : Fin n, (Finset.univ.filter fun a =>
        noiseViolation (seedD a) (seedM a) (seedR a) p idx).card ≤ c) :
    (Finset.univ.filter fun a =>
        ∃ idx : Fin n, noiseViolation (seedD a) (seedM a) (seedR a) p idx).card ≤ 256 * c := by
  refine le_trans (card_noiseFail_le_sum seedD seedM seedR p) ?_
  calc ∑ idx : Fin n, (Finset.univ.filter fun a =>
          noiseViolation (seedD a) (seedM a) (seedR a) p idx).card
      ≤ ∑ _idx : Fin n, c := Finset.sum_le_sum fun idx _ => hc idx
    _ = 256 * c := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end Fips203
