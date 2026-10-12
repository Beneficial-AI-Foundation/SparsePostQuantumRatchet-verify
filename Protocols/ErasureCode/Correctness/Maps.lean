/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Alessandro D'Angelo
-/
import Protocols.ErasureCode.Model.SPQRReedSolomon.Correctness
import Spqr.Math.Gf16.Equiv

/-! # Concrete SPQR byte and chunk representation maps -/

open Aeneas Aeneas.Std
open ErasureCode.SPQRReedSolomon

namespace Protocols.ErasureCode

private noncomputable def highByte (x : GF216) : U8 :=
  U8.ofNatCore (GF216.toNat x / 256) (by
    have h := GF216.toNat_lt x
    simp only [UScalarTy.U8_numBits_eq, Nat.reducePow]
    omega)

private noncomputable def lowByte (x : GF216) : U8 :=
  U8.ofNatCore (GF216.toNat x % 256) (by
    simp only [UScalarTy.U8_numBits_eq, Nat.reducePow]
    exact Nat.mod_lt _ (by omega))

@[simp] private theorem highByte_val (x : GF216) :
    (highByte x).val = GF216.toNat x / 256 := by
  simp only [highByte, U8.ofNatCore_val_eq]

@[simp] private theorem lowByte_val (x : GF216) :
    (lowByte x).val = GF216.toNat x % 256 := by
  simp only [lowByte, U8.ofNatCore_val_eq]

private theorem highByte_lowByte (x : GF216) :
    Nat.toGF216 (256 * (highByte x).val + (lowByte x).val) = x := by
  rw [highByte_val, lowByte_val]
  calc
    Nat.toGF216 (256 * (GF216.toNat x / 256) + GF216.toNat x % 256) =
        Nat.toGF216 (GF216.toNat x) := by congr 1; omega
    _ = x := GF216.toGF216_toNat x

private noncomputable def wordByte (x : GF216) (i : Nat) : U8 :=
  if i % 2 = 0 then highByte x else lowByte x

private noncomputable def chunkBytes (c : Chunk GF16) : List U8 :=
  List.ofFn fun i : Fin 32 =>
    wordByte (c ⟨i.val / 2, by omega⟩) i.val

private noncomputable def messageBytes {k : ℕ} (M : Fin k → Chunk GF16) : List U8 :=
  List.ofFn fun i : Fin (32 * k) =>
    wordByte (M ⟨i.val / 32, by omega⟩
      ⟨(i.val / 2) % 16, Nat.mod_lt _ (by omega)⟩) i.val

private theorem chunkBytes_even (c : Chunk GF16) (j : Fin 16) :
    (chunkBytes c)[2 * j.val]! = highByte (c j) := by
  have hdiv : 2 * j.val / 2 = j.val := by omega
  unfold chunkBytes
  rw [List.getElem!_ofFn _ _ (by omega)]
  simp [wordByte, hdiv]

private theorem chunkBytes_odd (c : Chunk GF16) (j : Fin 16) :
    (chunkBytes c)[2 * j.val + 1]! = lowByte (c j) := by
  have hdiv : (2 * j.val + 1) / 2 = j.val := by omega
  unfold chunkBytes
  rw [List.getElem!_ofFn _ _ (by omega)]
  simp [wordByte, hdiv]

private theorem messageBytes_even {k : ℕ} (M : Fin k → Chunk GF16)
    (m : Fin k) (c : Fin 16) :
    (messageBytes M)[2 * (16 * m.val + c.val)]! = highByte (M m c) := by
  have hm : 2 * (16 * m.val + c.val) / 32 = m.val := by omega
  unfold messageBytes
  rw [List.getElem!_ofFn _ _ (by omega)]
  simp [wordByte, hm, Nat.mod_eq_of_lt c.isLt]

private theorem messageBytes_odd {k : ℕ} (M : Fin k → Chunk GF16)
    (m : Fin k) (c : Fin 16) :
    (messageBytes M)[2 * (16 * m.val + c.val) + 1]! = lowByte (M m c) := by
  have hm : (2 * (16 * m.val + c.val) + 1) / 32 = m.val := by omega
  have hc : ((2 * (16 * m.val + c.val) + 1) / 2) % 16 = c.val := by omega
  unfold messageBytes
  rw [List.getElem!_ofFn _ _ (by omega)]
  simp [wordByte, hm, hc]

noncomputable def ofSpqrChunk (c : spqr.encoding.Chunk) : Chunk GF16 :=
  fun j => Nat.toGF216
    (256 * (c.data.val[2 * j.val]!).val + (c.data.val[2 * j.val + 1]!).val)

noncomputable def toSpqrChunk (p : Fin (2 ^ 16) × Chunk GF16) : spqr.encoding.Chunk where
  index := U16.ofNatCore p.1.val (by
    simpa only [UScalarTy.U16_numBits_eq] using p.1.isLt)
  data := ⟨chunkBytes p.2, by simp [chunkBytes]⟩

noncomputable def bytesOfMessage {k : ℕ} (hk : k ≤ 2 ^ 16)
    (M : Fin k → Chunk GF16) : Slice U8 :=
  ⟨messageBytes M, by
    simp only [messageBytes, List.length_ofFn]
    have := Usize.cMax_bound_concrete
    omega⟩

noncomputable def messageOfBytes (k : ℕ) (b : alloc.vec.Vec Std.U8) :
    Option (Fin k → Chunk GF16) :=
  if b.length = 32 * k then
    some fun m c => Nat.toGF216
      (256 * (b.val[2 * (16 * m.val + c.val)]!).val +
        (b.val[2 * (16 * m.val + c.val) + 1]!).val)
  else none

theorem bytesOfMessage_length {k : ℕ} (hk : k ≤ 2 ^ 16)
    (M : Fin k → Chunk GF16) :
    (bytesOfMessage hk M).length = 32 * k := by
  simp [bytesOfMessage, messageBytes]

theorem bytesOfMessage_pair {k : ℕ} (hk : k ≤ 2 ^ 16)
    (M : Fin k → Chunk GF16) (m : Fin k) (c : Fin 16) :
    Nat.toGF216 (256 * ((bytesOfMessage hk M).val[2 * (16 * m.val + c.val)]!).val
        + ((bytesOfMessage hk M).val[2 * (16 * m.val + c.val) + 1]!).val) = M m c := by
  change Nat.toGF216
    (256 * ((messageBytes M)[2 * (16 * m.val + c.val)]!).val +
      ((messageBytes M)[2 * (16 * m.val + c.val) + 1]!).val) = M m c
  rw [messageBytes_even, messageBytes_odd]
  exact highByte_lowByte (M m c)

theorem ofSpqrChunk_toSpqrChunk (p : Fin (2 ^ 16) × Chunk GF16) :
    ofSpqrChunk (toSpqrChunk p) = p.2 := by
  funext j
  change Nat.toGF216
    (256 * ((chunkBytes p.2)[2 * j.val]!).val +
      ((chunkBytes p.2)[2 * j.val + 1]!).val) = p.2 j
  rw [chunkBytes_even, chunkBytes_odd]
  exact highByte_lowByte (p.2 j)

theorem toSpqrChunk_index (p : Fin (2 ^ 16) × Chunk GF16) :
    (toSpqrChunk p).index.val = p.1.val := by
  simp [toSpqrChunk]

theorem messageOfBytes_some_iff (k : ℕ) (b : alloc.vec.Vec Std.U8) :
    (messageOfBytes k b).isSome ↔ b.length = 32 * k := by
  simp [messageOfBytes]

theorem messageOfBytes_eq_some_of_pairs (k : ℕ) (b : alloc.vec.Vec Std.U8)
    (M : Fin k → Chunk GF16) (hlen : b.length = 2 * (16 * k))
    (hpair : ∀ (m : Fin k) (c : Fin 16),
      Nat.toGF216 (256 * (b.val[2 * (16 * m.val + c.val)]!).val
          + (b.val[2 * (16 * m.val + c.val) + 1]!).val) = M m c) :
    messageOfBytes k b = some M := by
  unfold messageOfBytes
  split
  · congr
    funext m c
    exact hpair m c
  · rename_i h
    exfalso
    apply h
    omega

theorem messageOfBytes_bytesOfMessage {k : ℕ} (hk : k ≤ 2 ^ 16)
    (M : Fin k → Chunk GF16) :
    messageOfBytes k
      ⟨(bytesOfMessage hk M).val, by simpa using (bytesOfMessage hk M).property⟩ = some M := by
  apply messageOfBytes_eq_some_of_pairs
  · change (bytesOfMessage hk M).length = 2 * (16 * k)
    rw [bytesOfMessage_length]
    omega
  · exact bytesOfMessage_pair hk M

end Protocols.ErasureCode
