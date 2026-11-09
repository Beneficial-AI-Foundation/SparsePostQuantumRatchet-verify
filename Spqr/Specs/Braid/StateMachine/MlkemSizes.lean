/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import SrcTranslated.Funs
public import SrcTranslated.FunsExternal
public meta import Spqr.Auxiliary.SpecTags
public import Spqr.Specs.Braid.StateMachine.Relation
public import Spqr.Specs.Braid.StateMachine.Refinement

/-! # The ML-KEM 768 sizes, and the refinement without them as a premise

`Ciphertext1::<960>::len()`, `Ciphertext2::<128>::len()` and `pk2_len()` are definitions in
`SrcTranslated/FunsExternal.lean`, with the bodies that libcrux-ml-kem 0.0.7 has. So
`MlkemSizes` holds (`mlkemSizes`), and `recv_refines` and `run_refines` hold without it
(`recv_refines_of_codeAgrees`, `run_refines_of_codeAgrees`).

**Source**: spqr/src/incremental_mlkem768.rs:8-15; libcrux-ml-kem 0.0.7
src/ind_cca/incremental/types.rs:161,174 and src/mlkem.rs:31 -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.v1.chunked.states

open Braid

/-- The ML-KEM 768 sizes hold: the first ciphertext has 960 bytes, the second 128, and the
encapsulation key 1152. -/
theorem mlkemSizes : MlkemSizes := by
  unfold MlkemSizes incremental_mlkem768.CIPHERTEXT1_SIZE incremental_mlkem768.CIPHERTEXT2_SIZE
    incremental_mlkem768.ENCAPSULATION_KEY_SIZE
    libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1.len
    libcrux_ml_kem.ind_cca.incremental.types.Ciphertext2.len
    libcrux_ml_kem.mlkem768.incremental.pk2_len
  exact ⟨rfl, rfl, rfl⟩

/-- `recv_refines` without the size premise. Assume `CodeAgrees P` and `Refines s σ`. If
`States::recv` succeeds on `s`, then the model's `Receive()` on `σ` succeeds with a related
state and the code's key. -/
@[correctness_spec, braid_spec "§2.5",
  braid_deviation Deviation.futureEpochError Deviation.ct1AckAccepted Deviation.lateEkChunk]
theorem recv_refines_of_codeAgrees (P : CodePrims) (hP : CodeAgrees P) (s : States)
    (σ : State _ _) (h : Refines s σ) (msg : Message) (out : Recv)
    (hs : States.recv s msg = ok (.Ok out)) :
    ∃ σ', Braid.receive P σ (absMsg msg) = some (σ', out.key.map absKey) ∧
      Refines out.state σ' :=
  recv_refines P hP mlkemSizes s σ h msg out hs

/-- `run_refines` without the size premise. Assume `CodeAgrees P` and `Refines s σ`. Then every
run of the code from `s` is a run of the model from `σ`, with a related end state and the same
keys. -/
@[correctness_spec, braid_spec "§2.5",
  braid_deviation Deviation.futureEpochError Deviation.ct1AckAccepted Deviation.lateEkChunk]
theorem run_refines_of_codeAgrees (P : CodePrims) (hP : CodeAgrees P) {s s' : States}
    {ks : List EpochSecret} (hr : Run s s' ks) {σ : State _ _} (h : Refines s σ) :
    ∃ σ', Braid.Run P σ σ' (ks.map absKey) ∧ Refines s' σ' :=
  run_refines P hP mlkemSizes hr h

end spqr.v1.chunked.states
