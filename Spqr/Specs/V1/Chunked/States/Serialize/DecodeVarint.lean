/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import Spqr.Code.Funs

/-! # Spec theorem for `spqr::v1::chunked::states::serialize::decode_varint`

`decode_varint` reads a LEB128-style variable-length integer from the byte buffer `from`
starting at cursor `at`, advancing the cursor past the bytes it consumed.

We prove the cursor contract — the cursor never moves backwards, and on success it started
inside the buffer and ends within bounds — and, beyond it, functional correctness: on success
the returned value is the LEB128 decoding (`varintVal`) of the `n` consumed bytes — 7 payload
bits per byte, least-significant septet first, truncated to 64 bits — where byte `n-1` is the
terminator (high bit clear) and all earlier bytes are continuation bytes (high bit set).

**Source**: src/v1/chunked/states/serialize.rs (lines 151-182)
-/

open Aeneas Aeneas.Std Result ControlFlow Error

-- Use the no-overflow cast spec so `step` learns `(hcast .I32 i).val = i.val` directly,
-- avoiding bit-vector reasoning about the `i as i32` conversion inside the loop.
attribute [local step] UScalar.hcast_inBounds_spec

namespace spqr.v1.chunked.states.serialize

/-! ## Pure model -/

/-- LEB128 value of the `n` payload septets read from `bytes[start], …, bytes[start+n-1]`:
each byte contributes its low 7 bits, least-significant septet first. -/
def varintVal (bytes : List Std.U8) (start : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => varintVal bytes start n + (bytes[start + n]!.val % 128) * 2 ^ (7 * n)

theorem varintVal_lt (bytes : List Std.U8) (start : ℕ) (n : ℕ) :
    varintVal bytes start n < 2 ^ (7 * n) := by
  induction n with
  | zero => simp [varintVal]
  | succ n ih =>
    have hc : bytes[start + n]!.val % 128 ≤ 127 := by omega
    have hmul : bytes[start + n]!.val % 128 * 2 ^ (7 * n) ≤ 127 * 2 ^ (7 * n) :=
      Nat.mul_le_mul_right _ hc
    have hpow : 2 ^ (7 * (n + 1)) = 2 ^ (7 * n) * 128 := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    simp only [varintVal]
    omega

/-- The accumulator (reduced mod 2⁶⁴) stays below `2^(7n)` for any reachable `n ≤ 10`. -/
theorem varintVal_mod_lt (bytes : List Std.U8) (start : ℕ) {n : ℕ} (hn : n ≤ 10) :
    varintVal bytes start n % 2 ^ 64 < 2 ^ (7 * n) := by
  rcases Nat.lt_or_ge (7 * n) 64 with h | h
  · have h1 := varintVal_lt bytes start n
    have h2 : varintVal bytes start n < 2 ^ 64 :=
      lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.mod_eq_of_lt h2]
    exact h1
  · exact lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
      (Nat.pow_le_pow_right (by norm_num) h)

/-! ## Bit-twiddling lemmas

The loop accumulates with `out ||| ((byte &&& 0x7f) << 7*i)`.  Because `out < 2^(7i)`, the OR
is on disjoint bit ranges and coincides with addition (mod 2⁶⁴, accounting for the silent
truncation of the 10th byte's high bits). -/

/-- Disjoint bitwise OR is addition: if `a` fits below bit `s`, then
`a ||| b·2^s = a + b·2^s`.  Proved by splitting both sides with `/ 2^s` and `% 2^s`. -/
private theorem lor_two_pow_mul_eq_add {a b s : ℕ} (ha : a < 2 ^ s) :
    a ||| b * 2 ^ s = a + b * 2 ^ s := by
  have hpos : 0 < 2 ^ s := Nat.two_pow_pos s
  have hmod : (a ||| b * 2 ^ s) % 2 ^ s = a := by
    rw [Nat.or_mod_two_pow, Nat.mul_mod_left, Nat.mod_eq_of_lt ha, Nat.or_zero]
  have hdiv : (a ||| b * 2 ^ s) / 2 ^ s = b := by
    rw [Nat.or_div_two_pow, Nat.div_eq_of_lt ha, Nat.mul_div_cancel _ hpos, Nat.zero_or]
  have hsplit := Nat.div_add_mod (a ||| b * 2 ^ s) (2 ^ s)
  rw [hdiv, hmod] at hsplit
  rw [← hsplit, Nat.mul_comm, Nat.add_comm]

/-- The accumulation step at the `u64` level: OR-ing `c <<< s` (truncated to 64 bits) into an
accumulator `a < 2^s` is addition of `c·2^s` mod 2⁶⁴. -/
private theorem lor_shiftLeft_mod_eq_add {a c s : ℕ} (hs : s < 64) (ha : a < 2 ^ s) :
    a ||| c <<< s % 2 ^ 64 = (a + c * 2 ^ s) % 2 ^ 64 := by
  have hss : 2 ^ (64 - s) * 2 ^ s = 2 ^ 64 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hshift : c <<< s % 2 ^ 64 = c % 2 ^ (64 - s) * 2 ^ s := by
    rw [Nat.shiftLeft_eq, ← hss, Nat.mul_mod_mul_right]
  have hc' : c % 2 ^ (64 - s) < 2 ^ (64 - s) := Nat.mod_lt _ (by positivity)
  have hlt : a + c % 2 ^ (64 - s) * 2 ^ s < 2 ^ 64 := by
    have h1 : a + c % 2 ^ (64 - s) * 2 ^ s < (c % 2 ^ (64 - s) + 1) * 2 ^ s := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have h2 : (c % 2 ^ (64 - s) + 1) * 2 ^ s ≤ 2 ^ (64 - s) * 2 ^ s :=
      Nat.mul_le_mul_right _ hc'
    omega
  have hdecomp : a + c * 2 ^ s
      = a + c % 2 ^ (64 - s) * 2 ^ s + c / 2 ^ (64 - s) * 2 ^ 64 := by
    conv_lhs => rw [← Nat.div_add_mod c (2 ^ (64 - s))]
    rw [Nat.add_mul, Nat.mul_comm (2 ^ (64 - s)) (c / 2 ^ (64 - s)), Nat.mul_assoc, hss]
    omega
  rw [hshift, lor_two_pow_mul_eq_add ha, hdecomp, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hlt]

private theorem u64_size_eq_two_pow : Std.U64.size = 2 ^ 64 := by
  simp [Std.U64.size_def, Std.U64.numBits]

/-- For a byte value `b < 256`, testing the continuation bit: `b &&& 0x80 = 0 ↔ b < 128`. -/
private theorem and_128_eq_zero_iff {b : ℕ} (hb : b < 256) : b &&& 128 = 0 ↔ b < 128 := by
  have h : b &&& 128 = (b.testBit 7).toNat * 2 ^ 7 := by
    rw [show (128 : ℕ) = 2 ^ 7 by norm_num, Nat.and_two_pow]
  rw [h, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.lt_or_ge b 128 with hlt | hge
  · have hd : b / 2 ^ 7 = 0 := Nat.div_eq_of_lt (by omega)
    rw [hd]
    simp [hlt]
  · have hd : b / 2 ^ 7 = 1 := by omega
    rw [hd]
    norm_num
    omega

/-! ## Spec theorems -/

/-- **Spec theorem for `decode_varint_loop.body`** (one iteration of the scan):

Either `done` with the state unchanged (the continuation flag was already cleared, or the scan
bound `max_i` was reached), or `cont` having consumed byte `from[at+i]`: the counter advances
by one, the low 7 bits of the byte are OR-ed into the accumulator at position `7i` — which,
since `out < 2^(7i)`, is addition of `(byte % 128)·2^(7i)` mod 2⁶⁴ — and the new flag records
whether this byte was the terminator (high bit clear). -/
@[step]
theorem decode_varint_loop_body_spec
    (from1 : alloc.vec.Vec Std.U8) (at1 max_i : Std.Usize)
    (out : Std.U64) (i : Std.Usize) (done1 : Bool)
    (hmax10 : max_i.val ≤ 10)
    (hmaxlen : at1.val + max_i.val ≤ from1.length)
    (hout : out.val < 2 ^ (7 * i.val)) :
    decode_varint_loop.body from1 at1 max_i out i done1 ⦃
      (cf : ControlFlow (Std.U64 × Std.Usize × Bool) (Std.U64 × Std.Usize × Bool)) =>
      match cf with
      | .done s => s = (out, i, done1)
      | .cont (out', i', flag) =>
          done1 = false ∧ i.val < max_i.val ∧ i'.val = i.val + 1 ∧
          out'.val
            = (out.val + from1.val[at1.val + i.val]!.val % 128 * 2 ^ (7 * i.val)) % 2 ^ 64 ∧
          (flag = true ↔ from1.val[at1.val + i.val]!.val < 128) ⦄ := by
  unfold decode_varint_loop.body
  by_cases hlt : i < max_i
  · simp only [hlt, ↓reduceIte]
    by_cases hdone : done1
    · simp only [hdone, ↓reduceIte]
      simp
    · simp only [hdone, Bool.false_eq_true, ↓reduceIte]
      step*
      have hidx : at1.val + i.val < from1.length := by scalar_tac
      have hbyte : byte = from1.val[at1.val + i.val]! := by
        simp only [byte_post]
        rw [getElem!_pos from1.val (at1.val + i.val) (by scalar_tac)]
        simp [*]
      have h1 : i8.val = byte.val &&& 128 := by
        rw [i8_post1, UScalar.val_and]
        scalar_tac
      have h2 : byte.val &&& 128 = 0 ↔ byte.val < 128 := and_128_eq_zero_iff (by scalar_tac)
      refine ⟨by scalar_tac, by scalar_tac, ?_, ?_, ?_⟩
      · -- Accumulator equation
        have hs : 7 * i.val < 64 := by scalar_tac
        have hi2 : i2.val = byte.val := by
          rw [i2_post]
          scalar_tac
        have h127 : i3.val = byte.val % 128 := by
          have h : i3.val = byte.val &&& 127 := by
            rw [i3_post1, UScalar.val_and, hi2]
            scalar_tac
          rw [h, show (127 : ℕ) = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
        have hshift : (i5.val).toNat = 7 * i.val := by scalar_tac
        have hi6 : i6.val = i3.val <<< (7 * i.val) % 2 ^ 64 := by
          rw [i6_post1, hshift, u64_size_eq_two_pow]
        have hor : out1.val = out.val ||| i6.val := by rw [out1_post1, UScalar.val_or]
        rw [hor, hi6, h127, hbyte, lor_shiftLeft_mod_eq_add hs hout]
      · -- Terminator flag, forward direction
        intro hf
        try rw [← hbyte]
        have hz : i8 = 0#u8 := of_decide_eq_true hf
        have hv : i8.val = 0 := by simp [hz]
        omega
      · -- Terminator flag, backward direction
        intro hf
        have hf' : byte.val < 128 := by
          first
          | exact hf
          | (rw [hbyte]; exact hf)
        have hv : i8.val = 0 := by omega
        have hz : i8 = 0#u8 := by scalar_tac
        simp [hz]
  · simp only [hlt, ↓reduceIte]
    simp

/-- **Spec theorem for `decode_varint`'s loop** (`decode_varint_loop`), from its initial state
`(out, i, done) = (0, 0, false)`:

Under `max_i ≤ 10` and `at1 + max_i ≤ from.len()`, the loop terminates in a state
`(out, i, done)` with `i ≤ max_i` where `out` is the LEB128 value of the `i` consumed bytes
(mod 2⁶⁴), and if `done` is set then byte `i-1` was the terminator (high bit clear) and all
earlier bytes were continuation bytes (high bit set). -/
@[step]
theorem decode_varint_loop_spec
    (from1 : alloc.vec.Vec Std.U8) (at1 max_i : Std.Usize)
    (hmax10 : max_i.val ≤ 10)
    (hmaxlen : at1.val + max_i.val ≤ from1.length) :
    decode_varint_loop from1 at1 0#u64 0#usize false max_i ⦃
      (p : Std.U64 × Std.Usize × Bool) =>
        p.2.1.val ≤ max_i.val ∧
        p.1.val = varintVal from1.val at1.val p.2.1.val % 2 ^ 64 ∧
        (p.2.2 = true →
          1 ≤ p.2.1.val ∧
          from1.val[at1.val + p.2.1.val - 1]!.val < 128 ∧
          ∀ k < p.2.1.val - 1, 128 ≤ from1.val[at1.val + k]!.val) ⦄ := by
  unfold decode_varint_loop
  apply loop.spec_decr_nat
    (measure := fun (p : Std.U64 × Std.Usize × Bool) => max_i.val - p.2.1.val)
    (inv := fun (p : Std.U64 × Std.Usize × Bool) =>
      p.2.1.val ≤ max_i.val ∧
      p.1.val = varintVal from1.val at1.val p.2.1.val % 2 ^ 64 ∧
      (p.2.2 = true →
        1 ≤ p.2.1.val ∧
        from1.val[at1.val + p.2.1.val - 1]!.val < 128 ∧
        ∀ k < p.2.1.val - 1, 128 ≤ from1.val[at1.val + k]!.val) ∧
      (p.2.2 = false → ∀ k < p.2.1.val, 128 ≤ from1.val[at1.val + k]!.val))
    (post := fun (p : Std.U64 × Std.Usize × Bool) =>
      p.2.1.val ≤ max_i.val ∧
      p.1.val = varintVal from1.val at1.val p.2.1.val % 2 ^ 64 ∧
      (p.2.2 = true →
        1 ≤ p.2.1.val ∧
        from1.val[at1.val + p.2.1.val - 1]!.val < 128 ∧
        ∀ k < p.2.1.val - 1, 128 ≤ from1.val[at1.val + k]!.val))
  · intro ⟨out', i', done'⟩ hinv
    dsimp only at hinv
    obtain ⟨hi, hval, htrue, hfalse⟩ := hinv
    have hout : out'.val < 2 ^ (7 * i'.val) := by
      rw [hval]
      exact varintVal_mod_lt from1.val at1.val (by omega)
    step*
    cases r with
    | done s =>
      subst r_post
      dsimp only
      exact ⟨hi, hval, htrue⟩
    | cont s =>
      obtain ⟨out'', i'', flag⟩ := s
      obtain ⟨hd, hlt, hi'', hval'', hflag⟩ := r_post
      dsimp only
      refine ⟨by omega, ?_, ?_, ?_, by omega⟩
      · -- Value accumulation
        rw [hi'']
        simp only [varintVal]
        rw [hval'', hval, Nat.mod_add_mod]
      · -- Flag set: byte i' was the terminator, all earlier bytes were continuations
        intro hf
        have hb := hflag.mp hf
        refine ⟨by omega, ?_, ?_⟩
        · have h : at1.val + i''.val - 1 = at1.val + i'.val := by omega
          rw [h]
          exact hb
        · intro k hk
          exact hfalse hd k (by omega)
      · -- Flag clear: all i'+1 bytes so far are continuation bytes
        intro hf k hk
        rcases Nat.lt_or_ge k i'.val with h | h
        · exact hfalse hd k h
        · have hk' : k = i'.val := by omega
          subst hk'
          rcases Nat.lt_or_ge (from1.val[at1.val + i'.val]!.val) 128 with hcon | hge2
          · rw [hflag.mpr hcon] at hf
            simp at hf
          · exact hge2
  · dsimp only
    simp [varintVal]

/-- **Spec theorem for `spqr::v1::chunked::states::serialize::decode_varint`**:

The cursor never moves backwards and, on success, `decode_varint` consumed `n` bytes
(`1 ≤ n ≤ 10`, all within the buffer, so the starting cursor is in bounds and the final
cursor is at most `from.len()`), the returned value is the LEB128 decoding of those bytes
truncated to 64 bits, byte `n-1` is the terminator (high bit clear), and bytes `0, …, n-2`
are continuation bytes (high bit set). On failure the error is `MsgDecode` and the cursor is
returned unchanged. -/
@[step]
theorem decode_varint_spec
    (from1 : alloc.vec.Vec Std.U8) (at1 : Std.Usize) :
    decode_varint from1 at1 ⦃
      (p : (core.result.Result Std.U64 Error) × Std.Usize) =>
        at1.val ≤ p.2.val ∧
        (match p.1 with
         | .Ok v =>
            at1.val < from1.length ∧
            ∃ n, p.2.val = at1.val + n ∧ 1 ≤ n ∧ n ≤ 10 ∧
              at1.val + n ≤ from1.length ∧
              v.val = varintVal from1.val at1.val n % 2 ^ 64 ∧
              from1.val[at1.val + n - 1]!.val < 128 ∧
              ∀ k < n - 1, 128 ≤ from1.val[at1.val + k]!.val
         | .Err e => e = Error.MsgDecode ∧ p.2 = at1) ⦄ := by
  unfold decode_varint
  by_cases hge : at1 ≥ alloc.vec.Vec.len from1
  · simp only [hge, ↓reduceIte]
    exact ⟨by scalar_tac, by simp⟩
  · simp only [hge, ↓reduceIte, core.cmp.min, MAX_VARINT_BYTES_LEN]
    step*
    have hd : done1 = true := by assumption
    obtain ⟨h1, h2, h3⟩ := out_post3 hd
    exact ⟨by scalar_tac, by scalar_tac, i3.val, at2_post, h1, by scalar_tac, by scalar_tac,
      out_post2, h2, h3⟩

end spqr.v1.chunked.states.serialize
