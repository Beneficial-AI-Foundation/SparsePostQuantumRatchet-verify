/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Alessandro D'Angelo
-/
import Protocols.ErasureCode.Correctness.Params
import Spqr.Math.Poly.Lagrange.Interpolant
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.EncodeBytes
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAt

/-! # Concrete encoder and its model correspondence -/

open Aeneas Aeneas.Std Result Polynomial
open ErasureCode.SPQRReedSolomon

namespace Protocols.ErasureCode

private theorem sum_scaledLagrangeBasis_eq_interpolate_of_val_eq
    {N : Usize} {k : ℕ} (hNk : N.val = k) (hN : N.val ≤ 2 ^ 16)
    (y : Fin k → GF216) :
    (∑ m : Fin k,
        Polynomial.C (y m) *
          spqr.encoding.polynomial.scaledLagrangeBasis N m.val) =
      Lagrange.interpolate Finset.univ
        (fun m : Fin k => Nat.toGF216 m.val) y := by
  subst k
  exact spqr.encoding.polynomial.sum_scaledLagrangeBasis_eq_interpolate hN y

noncomputable def encodeConcrete (k : ℕ) (hk : k ≤ 2 ^ 16)
    (M : Fin k → Chunk GF16) (i : Fin (2 ^ 16)) : Chunk GF16 :=
  match spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder.encode_bytes
      (bytesOfMessage hk M) with
  | .ok (.Ok enc) =>
      match spqr.encoding.polynomial.PolyEncoder.chunk_at enc
          (U16.ofNatCore i.val (by
            simpa only [UScalarTy.U16_numBits_eq] using i.isLt)) with
      | .ok (c, _) => ofSpqrChunk c
      | _ => default
  | _ => default

theorem encode_toModel (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k)
    (hk_tab : k ∈ ({1, 3, 5, 30, 34, 36} : Finset ℕ))
    (M : Fin k → Chunk GF16) (i : Fin (2 ^ 16)) :
    encodeConcrete k hk M i = (modelEC k hk hk_pos).encode M i := by
  classical
  have hk_cases := hk_tab
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk_cases
  have hk_le : k ≤ 36 := by
    omega
  have hmsg_len := bytesOfMessage_length hk M
  have h_even : (bytesOfMessage hk M).length % 2 = 0 := by
    rw [hmsg_len]
    omega
  have h_len : (bytesOfMessage hk M).length ≤ 2 ^ 16 * 16 := by
    rw [hmsg_len]
    omega
  obtain ⟨r, hencode, hr⟩ := WP.spec_imp_exists
    (spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder.encode_bytes_spec
      (bytesOfMessage hk M) h_even h_len)
  cases r with
  | Err err => simp at hr
  | Ok enc =>
    cases enc with
    | mk encIdx state =>
      cases state with
      | Polys polys => simp at hr
      | Points pts =>
        simp only at hr
        have hpts_length (j : ℕ) (hj : j < 16) :
            (pts[j]!).value.length = k := by
          rw [hr.2.1 j hj, hmsg_len]
          rw [show 32 * k / 2 = 16 * k from by omega, show (16 * k) % 16 = 0 from by omega,
            show 16 * k / 16 = k from by omega]
          simp
        let idx : U16 := U16.ofNatCore i.val (by
          simpa only [UScalarTy.U16_numBits_eq] using i.isLt)
        have hidx_val : idx.val = i.val := by
          simp only [idx, U16.ofNatCore_val_eq]
        have hidx_overflow : idx.val * 16 + 16 ≤ Usize.max := by
          have hmax := Usize.cMax_bound_concrete.1
          omega
        have hadmissible : ∀ (j : Nat), j < 16 →
            let len := (pts[j]!).value.length
            len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
            len = 30 ∨ len = 34 ∨ len = 36 := by
          intro j hj
          simp only [hpts_length j hj]
          omega
        obtain ⟨out, hchunk, hout⟩ := WP.spec_imp_exists
          (spqr.encoding.polynomial.PolyEncoder.chunk_at_spec_points
            { idx := encIdx, s := .Points pts } idx pts rfl
            hidx_overflow hadmissible)
        rcases out with ⟨chunk, enc'⟩
        simp only at hout
        have hconcrete : encodeConcrete k hk M i = ofSpqrChunk chunk := by
          simp only [encodeConcrete, hencode, idx, hchunk]
        rw [hconcrete]
        funext c
        unfold ofSpqrChunk
        rw [hout.2.2 c.val c.isLt]
        have hstored (m : Fin k) :
            ((pts[c.val]!).value[m.val]!).toGF216 = M m c := by
          rw [alloc.vec.Vec.getElem!_Nat_eq]
          rw [spqr.encoding.polynomial.getElem!_toGF216_eq_coeff]
          rw [(hr.2.2 c.val c.isLt m.val (by
            rw [hpts_length c.val c.isLt]
            exact m.isLt)).2]
          have hoffset : c.val + 16 * m.val = 16 * m.val + c.val := by omega
          rw [hoffset]
          simp only [Slice.getElem!_Nat_eq]
          exact bytesOfMessage_pair hk M m c
        have hpoly :
            (∑ n ∈ Finset.range (pts[c.val]!).value.length,
                Polynomial.C (((pts[c.val]!).value[n]!).toGF216) *
                  spqr.encoding.polynomial.scaledLagrangeBasis
                    (pts[c.val]!).value.len n) =
              Lagrange.interpolate Finset.univ
                (fun m : Fin k => Nat.toGF216 m.val) (fun m => M m c) := by
          rw [hpts_length c.val c.isLt]
          rw [← Fin.sum_univ_eq_sum_range]
          simp_rw [hstored]
          exact sum_scaledLagrangeBasis_eq_interpolate_of_val_eq
            (by rw [alloc.vec.Vec.len_val, hpts_length c.val c.isLt])
            (by rw [alloc.vec.Vec.len_val, hpts_length c.val c.isLt]; exact hk)
            (fun m => M m c)
        rw [hpoly, hidx_val]
        rfl

end Protocols.ErasureCode
