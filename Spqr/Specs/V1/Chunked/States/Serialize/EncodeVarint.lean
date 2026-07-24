/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs
import Spqr.Specs.Aeneas.RangeIteratorNext
import Spqr.Specs.V1.Chunked.States.Serialize.MAX_VARINT_BYTES_LEN

/-! # Spec theorem for `spqr::v1::chunked::states::serialize::encode_varint`

`encode_varint` appends the LEB128-style variable-length encoding of `a : u64` to the byte
buffer `into`: each output byte carries the next 7 low bits of `a` (least-significant septet
first); continuation bytes have the high bit set and the final byte has it clear.

We prove functional correctness: the result is exactly `into` extended with `varintBytes a`,
the pure LEB128 byte encoding of `a` (between 1 and 10 bytes for a `u64`).  The precondition
`into.len() + 10 ≤ usize::MAX` discharges the overflow guard of the pushes.

**Source**: src/v1/chunked/states/serialize.rs (lines 139-149)
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace spqr.v1.chunked.states.serialize

/-! ## Pure model -/

/-- LEB128 byte encoding of `a`: 7 payload bits per byte, least-significant septet first.
Every byte except the last has the continuation bit (`0x80`) set; the last byte — the most
significant septet — has it clear. -/
def varintBytes (a : ℕ) : List ℕ :=
  if a < 128 then [a] else (a % 128 + 128) :: varintBytes (a / 128)
termination_by a
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

theorem varintBytes_of_lt {a : ℕ} (h : a < 128) : varintBytes a = [a] := by
  rw [varintBytes]
  simp [h]

theorem varintBytes_of_ge {a : ℕ} (h : 128 ≤ a) :
    varintBytes a = (a % 128 + 128) :: varintBytes (a / 128) := by
  rw [varintBytes]
  simp [Nat.not_lt.mpr h]

theorem varintBytes_length_pos (a : ℕ) : 1 ≤ (varintBytes a).length := by
  rw [varintBytes]
  split <;> simp

/-- A value below `2^(7n)` encodes in at most `n` bytes. -/
theorem varintBytes_length_le : ∀ (n a : ℕ), 1 ≤ n → a < 2 ^ (7 * n) →
    (varintBytes a).length ≤ n
  | 1, a, _, h => by
    rw [varintBytes_of_lt (by omega)]
    simp
  | n + 2, a, _, h => by
    by_cases ha : a < 128
    · rw [varintBytes_of_lt ha]
      simp
    · rw [varintBytes_of_ge (by omega)]
      have hsplit : 2 ^ (7 * (n + 2)) = 2 ^ (7 * (n + 1)) * 128 := by
        rw [show 7 * (n + 2) = 7 * (n + 1) + 7 by ring, Nat.pow_add]
      have hdiv : a / 128 < 2 ^ (7 * (n + 1)) :=
        Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
      have := varintBytes_length_le (n + 1) (a / 128) (by omega) hdiv
      simp only [List.length_cons]
      omega

/-- A `u64` value encodes in at most 10 bytes. -/
theorem varintBytes_length_le_ten {a : ℕ} (h : a < 2 ^ 64) : (varintBytes a).length ≤ 10 :=
  varintBytes_length_le 10 a (by omega)
    (lt_of_lt_of_le h (by norm_num))

/-- Mirror of the Rust unit test `encoding_varint`: `0x012C` encodes to `[0xAC, 0x02]`. -/
example : varintBytes 0x012C = [0xAC, 0x02] := by
  rw [varintBytes_of_ge (by norm_num), varintBytes_of_lt (by norm_num)]

/-! ## Bit-twiddling lemma -/

/-- Setting the continuation bit on a 7-bit payload is addition: for `b < 128`,
`0x80 ||| b = 128 + b`.  The bit ranges are disjoint, so the OR splits cleanly with
`/ 128` and `% 128`. -/
private theorem or_128_eq_add {b : ℕ} (hb : b < 128) : 128 ||| b = 128 + b := by
  have hmod : (128 ||| b) % 2 ^ 7 = b := by
    rw [Nat.lor_comm, Nat.or_mod_two_pow, Nat.mod_eq_of_lt hb]
    norm_num
  have hdiv : (128 ||| b) / 2 ^ 7 = 1 := by
    rw [Nat.lor_comm, Nat.or_div_two_pow, Nat.div_eq_of_lt hb]
    norm_num
  have hsplit := Nat.div_add_mod (128 ||| b) (2 ^ 7)
  rw [hdiv, hmod] at hsplit
  omega

/-! ## Spec theorems -/

/-- **Spec theorem for `encode_varint_loop.body`** (one iteration of the encoder):

Either the range is exhausted (`done` with the buffer unchanged), or the low 7 bits of `a`
are emitted: if `a < 128` the loop finishes (`done`) having pushed the terminator byte `a`;
otherwise it continues (`cont`) having pushed the continuation byte `a % 128 + 128`, with
the iterator advanced by one and `a` shifted down 7 bits to `a / 128`. -/
@[step]
theorem encode_varint_loop_body_spec
    (iter : core.ops.range.Range Std.Usize) (a : Std.U64) (into : alloc.vec.Vec Std.U8)
    (hlen : into.length < Std.Usize.max) :
    encode_varint_loop.body iter a into ⦃
      (cf : ControlFlow ((core.ops.range.Range Std.Usize) × Std.U64 ×
        (alloc.vec.Vec Std.U8)) (alloc.vec.Vec Std.U8)) =>
      match cf with
      | .done out =>
          (iter.end.val ≤ iter.start.val ∧ out = into) ∨
          (iter.start.val < iter.end.val ∧ a.val < 128 ∧
            ∃ b : Std.U8, out.val = into.val ++ [b] ∧ b.val = a.val)
      | .cont (iter', a', into') =>
          iter.start.val < iter.end.val ∧ 128 ≤ a.val ∧
          iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end ∧
          a'.val = a.val / 128 ∧
          ∃ b : Std.U8, into'.val = into.val ++ [b] ∧ b.val = a.val % 128 + 128 ⦄ := by
  unfold encode_varint_loop.body
  obtain ⟨⟨opt, iter1⟩, hnext, h_none, h_some⟩ :=
    WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_spec' iter)
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases hlt : iter.start.val < iter.end.val
  · obtain ⟨h_opt, h_start, h_end⟩ := h_some hlt
    rw [h_opt]
    by_cases ha : a < 128#u64
    · simp only [ha, ↓reduceIte]
      step*
      have hi : i.val = a.val % 128 := by
        have h : i.val = a.val &&& 127 := by
          rw [i_post1, UScalar.val_and]
          scalar_tac
        rw [h, show (127 : ℕ) = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      have hb : byte.val = a.val % 128 := by
        rw [byte_post, UScalar.cast_val_eq, hi,
          show UScalarTy.U8.numBits = 8 from rfl]
        omega
      right
      refine ⟨hlt, by scalar_tac, byte, into1_post, ?_⟩
      have halt : a.val < 128 := by scalar_tac
      omega
    · simp only [ha, ↓reduceIte]
      step*
      have hi : i.val = a.val % 128 := by
        have h : i.val = a.val &&& 127 := by
          rw [i_post1, UScalar.val_and]
          scalar_tac
        rw [h, show (127 : ℕ) = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      have hb : byte.val = a.val % 128 := by
        rw [byte_post, UScalar.cast_val_eq, hi,
          show UScalarTy.U8.numBits = 8 from rfl]
        omega
      have hblt : byte.val < 128 := by omega
      have hi1 : i1.val = a.val % 128 + 128 := by
        have h : i1.val = 128 ||| byte.val := by
          rw [i1_post1, UScalar.val_or]
          scalar_tac
        rw [h, or_128_eq_add hblt, hb]
        omega
      have ha1 : a1.val = a.val / 128 := by
        rw [a1_post1, Nat.shiftRight_eq_div_pow]
      exact ⟨hlt, by scalar_tac, h_start, h_end, ha1, i1, into1_post, hi1⟩
  · obtain ⟨h_opt, h_iter⟩ := h_none hlt
    rw [h_opt]
    grind

/-- **Spec theorem for `encode_varint`'s loop** (`encode_varint_loop`), from the initial
iterator `0..MAX_VARINT_BYTES_LEN`:

The loop always terminates via the terminator branch (a `u64` shifted down 7 bits nine
times is below 128, so the 10-iteration budget is never exhausted) and the buffer is
extended with exactly the LEB128 encoding of `a`. -/
@[step]
theorem encode_varint_loop_spec
    (a : Std.U64) (into : alloc.vec.Vec Std.U8)
    (hlen : into.length + 10 ≤ Std.Usize.max) :
    encode_varint_loop { start := 0#usize, «end» := MAX_VARINT_BYTES_LEN } a into ⦃
      (out : alloc.vec.Vec Std.U8) =>
      ∃ tail, out.val = into.val ++ tail ∧ tail.map UScalar.val = varintBytes a.val ∧
        1 ≤ tail.length ∧ tail.length ≤ 10 ⦄ := by
  unfold encode_varint_loop
  apply loop.spec_decr_nat
    (measure := fun (p : (core.ops.range.Range Std.Usize) × Std.U64 ×
      (alloc.vec.Vec Std.U8)) => 10 - p.1.start.val)
    (inv := fun (p : (core.ops.range.Range Std.Usize) × Std.U64 ×
      (alloc.vec.Vec Std.U8)) =>
      p.1.end.val = 10 ∧ p.1.start.val ≤ 9 ∧
      p.2.1.val = a.val / 128 ^ p.1.start.val ∧
      ∃ tail, p.2.2.val = into.val ++ tail ∧ tail.length = p.1.start.val ∧
        tail.map UScalar.val ++ varintBytes p.2.1.val = varintBytes a.val)
    (post := fun (out : alloc.vec.Vec Std.U8) =>
      ∃ tail, out.val = into.val ++ tail ∧ tail.map UScalar.val = varintBytes a.val ∧
        1 ≤ tail.length ∧ tail.length ≤ 10)
  · rintro ⟨iter', a', into'⟩ ⟨h_end, h_start, h_a, tail, h_into, h_tlen, h_tmap⟩
    dsimp only at h_end h_start h_a h_into h_tlen h_tmap ⊢
    have hlen' : into'.length < Std.Usize.max := by
      have h : into'.val.length = into.val.length + tail.length := by
        simp [h_into]
      scalar_tac
    step*
    cases r with
    | done out =>
      rcases r_post with ⟨hex, _⟩ | ⟨_, ha_small, b, h_out, h_bval⟩
      · omega
      · refine ⟨tail ++ [b], ?_, ?_, by simp, ?_⟩
        · rw [h_out, h_into, List.append_assoc]
        · rw [List.map_append, List.map_cons, List.map_nil, h_bval,
            ← varintBytes_of_lt ha_small, h_tmap]
        · have hlt10 : (varintBytes a.val).length ≤ 10 :=
            varintBytes_length_le_ten (by scalar_tac)
          have hlen_eq := congrArg List.length h_tmap
          rw [varintBytes_of_lt ha_small] at hlen_eq
          simp at hlen_eq ⊢
          omega
    | cont s =>
      obtain ⟨iter'', a'', into''⟩ := s
      obtain ⟨hlt, ha_big, h_start'', h_end'', h_a'', b, h_into'', h_bval⟩ := r_post
      have h9 : iter'.start.val ≤ 8 := by
        by_contra hgt
        have h9' : iter'.start.val = 9 := by omega
        rw [h_a, h9'] at ha_big
        have hmul : 128 * 128 ^ 9 ≤ a.val :=
          (Nat.le_div_iff_mul_le (by positivity)).mp ha_big
        rw [show (128 : ℕ) * 128 ^ 9 = 1180591620717411303424 from by norm_num] at hmul
        scalar_tac
      have h_end_val : iter''.end.val = iter'.end.val := by rw [h_end'']
      dsimp only
      refine ⟨by omega, by omega, ?_, ⟨tail ++ [b], ?_, ?_, ?_⟩, by omega⟩
      · rw [h_a'', h_a, h_start'', Nat.div_div_eq_div_mul, ← Nat.pow_succ]
      · rw [h_into'', h_into, List.append_assoc]
      · simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · rw [List.map_append, List.map_cons, List.map_nil, h_bval, h_a'',
          List.append_assoc, List.singleton_append, ← varintBytes_of_ge ha_big, h_tmap]
  · dsimp only
    refine ⟨by simp, by scalar_tac, by simp, [], by simp, by scalar_tac, by simp⟩

/-- **Spec theorem for `spqr::v1::chunked::states::serialize::encode_varint`**:

Under the no-overflow precondition `into.len() + 10 ≤ usize::MAX`, `encode_varint a into`
succeeds and returns `into ++ tail` where `tail` (as natural-number byte values) is exactly
`varintBytes a`, the LEB128 encoding of `a`: between 1 and 10 bytes, 7 payload bits per byte
least-significant first, every byte except the last carrying the continuation bit `0x80`. -/
@[step]
theorem encode_varint_spec
    (a : Std.U64) (into : alloc.vec.Vec Std.U8)
    (hlen : into.length + 10 ≤ Std.Usize.max) :
    encode_varint a into ⦃ (out : alloc.vec.Vec Std.U8) =>
      ∃ tail, out.val = into.val ++ tail ∧ tail.map UScalar.val = varintBytes a.val ∧
        1 ≤ tail.length ∧ tail.length ≤ 10 ⦄ := by
  unfold encode_varint
  exact encode_varint_loop_spec a into hlen

end spqr.v1.chunked.states.serialize
