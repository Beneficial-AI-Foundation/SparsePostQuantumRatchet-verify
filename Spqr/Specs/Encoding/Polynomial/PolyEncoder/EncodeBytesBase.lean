/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.NUM_POLYS
import Spqr.Specs.Aeneas.SliceChunksExact
import Spqr.Specs.Encoding.Gf.GF16.New

/-! # Spec theorem for `PolyEncoder::encode_bytes_base`: loop body 0

Message bytes are distributed round-robin across `NUM_POLYS = 16` `Point` arrays. Each 2-byte
chunk `(c[0], c[1])` is big-endian decoded to a GF(2¹⁶) element via `GF16::new` and appended to
`pts[i % 16].value`.

The body calls `next` on `Enumerate<ChunksExact<u8>>`, yielding `(i, c)`, then pushes
`GF16::new(((c[0] as u16) << 8) + (c[1] as u16))` onto `pts[i % 16].value`.

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf spqr.math.gf

namespace spqr.encoding.polynomial.PolyEncoder.encode_bytes_base_loop

instance : Inhabited encoding.polynomial.Point := ⟨⟨alloc.vec.Vec.new _⟩⟩

/-- **Spec theorem for `encode_bytes_base_loop.body`** (nat-level):

Big-endian decode of a 2-byte chunk into GF(2¹⁶), followed by round-robin insertion into `pts`.

  • **done**: `pts' = pts` — iterator exhausted.
  • **cont**: `g.toGF216 = ((c[0]! * 256) + c[1]!).toGF216` and `g` is pushed onto
    `pts[i % 16].value`, other entries unchanged. -/
@[step]
theorem body_spec
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.ChunksExact U8))
    (pts : Array Point 16#usize)
    (h_push_ok : ∀ j < 16, (pts[j]!).value.length + 1 ≤ Usize.max)
    (h_chunks_len : ∀ c ∈ iter.iter.chunks, c.length ≥ 2)
    (h_count_bound : iter.iter.chunks ≠ [] → iter.count + 1 ≤ Usize.max) :
    body iter pts ⦃ cf =>
      match cf with
      | ControlFlow.done pts' => pts' = pts
      | ControlFlow.cont (_, pts') =>
          ∃ (i : Usize) (c : Slice U8) (g : GF16),
            c.length ≥ 2 ∧
            g.toGF216 = (256 * c[0]! + c[1]!).toGF216 ∧
            pts'[i.val % 16]!.value = (pts[i.val % 16]!).value ++ [g] ∧
            (∀ k, k ≠ i.val % 16 → pts'[k]! = pts[k]!) ⦄ := by
  unfold body
  simp only [
    core.iter.adapters.enumerate.IteratorEnumerate.next,
    core.slice.iter.IteratorChunksExact.next]
  split
  · simp [WP.spec_ok]
  · rename_i hd tl rest
    simp only [bind_tc_ok]
    have h_c_len : hd.val.length ≥ 2 := h_chunks_len hd (by rw [rest]; exact .head _)
    have h_count_ok : iter.count.val + 1 ≤ Usize.max :=
      h_count_bound (by rw [rest]; exact List.cons_ne_nil _ _)
    step*
    · simp_all
      grind
    refine ⟨iter.count, hd, g, ?_, ?_, ?_, ?_⟩
    · exact h_c_len
    · conv_lhs =>
        simp[g_post,i7_post,i4_post1,i6_post, i3_post, i2_post, i5_post]
      congr
      · rw[Nat.shiftLeft_eq]
        simp only [Nat.reducePow]
        have :(↑(hd)[0] * 256) < U16.size := by scalar_tac
        have := Nat.mod_eq_of_lt this
        grind
      · grind
    · simp_all
      grind
    · intro k hk
      simp_all

private theorem body_spec_with_iter
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.ChunksExact U8))
    (pts : Array Point 16#usize)
    (h_push_ok : ∀ (j : Nat), j < 16 → (pts[j]!).value.length + 1 ≤ Usize.max)
    (h_chunks_len : ∀ c ∈ iter.iter.chunks, c.length ≥ 2)
    (h_count_bound : iter.iter.chunks ≠ [] → iter.count + 1 ≤ Usize.max) :
    body iter pts ⦃ cf =>
      match cf with
      | ControlFlow.done pts' =>
          pts' = pts ∧ iter.iter.chunks = []
      | ControlFlow.cont (iter', pts') =>
          (∃ hd tl, iter.iter.chunks = hd :: tl ∧ iter'.iter.chunks = tl) ∧
          iter'.count.val + iter'.iter.chunks.length =
            iter.count.val + iter.iter.chunks.length ∧
          ∃ (i : Usize) (c : Slice U8) (g : GF16),
            c.length ≥ 2 ∧
            g.toGF216 = (256 * c[0]! + c[1]!).toGF216 ∧
            pts'.val[i.val % 16]!.value =
              (pts[i.val % 16]!).value ++ [g] ∧
            (∀ k, k ≠ i.val % 16 → pts'[k]! = pts[k]!) ⦄ := by
  unfold body
  simp only [
    core.iter.adapters.enumerate.IteratorEnumerate.next,
    core.slice.iter.IteratorChunksExact.next]
  split
  · rename_i h_nil
    simp only [bind_tc_ok, GF16.new_eq, uncurry_apply_pair, ↓existsAndEq, and_true, ge_iff_le,
      List.getElem!_eq_getElem?_getD, ne_eq, exists_and_left, WP.spec_ok, true_and]
    exact h_nil
  · rename_i hd tl rest
    simp only [bind_tc_ok]
    have h_c_len : hd.val.length ≥ 2 :=
      h_chunks_len hd (by rw [rest]; exact .head _)
    have h_count_ok : iter.count.val + 1 ≤ Usize.max :=
      h_count_bound (by rw [rest]; exact List.cons_ne_nil _ _)
    step*
    · simp_all
      grind
    constructor
    · use hd
    constructor
    · simp_all
      omega
    · refine ⟨iter.count, hd, g, h_c_len, ?_, ?_, ?_⟩
      · conv_lhs =>
          simp[g_post,i7_post,i4_post1,i6_post, i3_post, i2_post, i5_post]
        congr
        · rw[Nat.shiftLeft_eq]
          simp only [Nat.reducePow]
          have :(↑(hd)[0] * 256) < U16.size := by scalar_tac
          have := Nat.mod_eq_of_lt this
          grind
        · grind
      · simp_all
        grind
      · intro k hk
        simp_all

/-! # Spec theorem for `PolyEncoder::encode_bytes_base`: loop 0

The loop `encode_bytes_base_loop` iterates over `Enumerate<ChunksExact<u8>>`, performing
round-robin distribution of big-endian–decoded GF(2¹⁶) elements into 16 `Point` value vectors.

Each step calls `next` to obtain `(i, c)`, computes `poly = i % 16`, decodes
`g := GF16::new(((c[0] as u16) << 8) + (c[1] as u16))`, and pushes `g` onto `pts[poly].value`.

**Loop invariant**: remaining chunks are valid 2-byte slices, push overflow is safe, each
point's value list is a prefix of the final list, and every appended element is a valid
big-endian GF(2¹⁶) decode.

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem loop_spec
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.ChunksExact U8))
    (pts : Array Point 16#usize)
    (h_push_ok : ∀ (j : Nat), j < 16 →
        (pts[j]!).value.length + iter.iter.chunks.length ≤ Usize.max)
    (h_chunks_len : ∀ c ∈ iter.iter.chunks, c.length ≥ 2)
    (h_count_chunks : iter.count + iter.iter.chunks.length ≤ Usize.max) :
    encode_bytes_base_loop iter pts ⦃ (pts' : Array Point 16#usize) =>
      (∀ (j : Nat), j < 16 →
        ∃ (suffix : List GF16),
          pts'[j]!.value = pts[j]!.value ++ suffix ∧
          (∀ g ∈ suffix,
            ∃ (c : Slice U8),
              c.length ≥ 2 ∧
              g.toGF216 = (256 * c[0]!+ c[1]!).toGF216)) ⦄ := by
  unfold encode_bytes_base_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.iter.adapters.enumerate.Enumerate (core.slice.iter.ChunksExact U8) ×
                  Array Point 16#usize) => p.1.iter.chunks.length)
    (inv := fun (p : core.iter.adapters.enumerate.Enumerate (core.slice.iter.ChunksExact U8) ×
                    Array Point 16#usize) =>
        (∀ c ∈ p.1.iter.chunks, c.length ≥ 2) ∧
        (∀ (j : Nat), j < 16 → (p.2[j]!).value.length + p.1.iter.chunks.length ≤ Usize.max) ∧
        (p.1.count + p.1.iter.chunks.length ≤ Usize.max) ∧
        (∀ (j : Nat), j < 16 →
          ∃ (suffix : List GF16),
            p.2[j]!.value = pts[j]!.value ++ suffix ∧
            (∀ g ∈ suffix,
              ∃ (c : Slice U8),
                c.length ≥ 2 ∧
                g.toGF216 = (256 * c[0]! + c[1]!).toGF216)))
  · rintro ⟨iter', pts'⟩ ⟨h_chunks', h_push', h_count', h_pre'⟩
    simp only [] at h_chunks' h_push' h_count' h_pre' ⊢
    cases h_chunks_cases : iter'.iter.chunks with
    | nil =>
      unfold body
      simp only [
        core.iter.adapters.enumerate.IteratorEnumerate.next,
        core.slice.iter.IteratorChunksExact.next,
        h_chunks_cases]
      simp only [bind_tc_ok, GF16.new_eq, uncurry_apply_pair,
        ge_iff_le, List.length_nil, not_lt_zero, and_false, WP.spec_ok]
      intro j hj
      simp_all
    | cons hd₀ tl₀ =>
      have h_push_one : ∀ (j : Nat), j < 16 →
          (pts'.val[j]!).value.val.length + 1 ≤ Usize.max := by grind
      have h_count_ok : iter'.iter.chunks ≠ [] → iter'.count.val + 1 ≤ Usize.max := by grind
      have h_body := body_spec_with_iter iter' pts' (by grind) h_chunks' h_count_ok
      apply WP.spec_mono h_body
      intro cf h_cf
      match cf with
      | ControlFlow.done pts'' => grind
      | ControlFlow.cont (iter'', pts'') =>  grind
  · exact ⟨h_chunks_len, by grind, h_count_chunks,
           fun j _ => ⟨[], by simp, fun _ h => absurd h (by grind)⟩⟩

end spqr.encoding.polynomial.PolyEncoder.encode_bytes_base_loop

/-! # Spec theorem for `spqr::encoding::polynomial::{PolyEncoder}::encode_bytes_base`

Encodes a byte-slice message `msg` into a `PolyEncoder` by:
  1. **Validation** — `msg.len()` must be even and ≤ `2^16 * 16`.
  2. **Initialization** — `from_fn` creates 16 empty `Point`s.
  3. **Distribution** — `chunks_exact(2).enumerate()` distributes big-endian–decoded GF(2¹⁶)
     elements round-robin into `pts[i % 16].value`.
  4. **Construction** — returns `Ok(PolyEncoder { idx: 0, s: Points(pts) })`.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyEncoder

/-- The `from_fn` closure always succeeds, returning a `Point` with an empty value vector. -/
private theorem call_mut_ok
    (c : PolyEncoder.encode_bytes_base.closure) (i : Usize) :
    PolyEncoder.encode_bytes_base.closure.Insts.CoreOpsFunctionFnMutTupleUsizePoint.call_mut
      c i = ok (⟨alloc.vec.Vec.new encoding.gf.GF16⟩, c) := by
  unfold
    PolyEncoder.encode_bytes_base.closure.Insts.CoreOpsFunctionFnMutTupleUsizePoint.call_mut
  have h_div : ∃ z, (Slice.len c) / 2#usize = ok z := by
    obtain ⟨z, hz, _⟩ := UScalar.div_spec (Slice.len c) (y := 2#usize) (by decide)
    exact ⟨z, hz⟩
  obtain ⟨z, hz⟩ := h_div
  simp only [hz, bind_tc_ok, alloc.vec.Vec.with_capacity]

/-- Any GF(2¹⁶) element `g` has a 2-byte slice `c` with
`g.toGF216 = ((256 * c[0] + c[1]).toGF216)`, via Euclidean division by 256. -/
private theorem gf16_representable (g : GF16) :
    ∃ (c : Slice U8),
      c.length ≥ 2 ∧
      g.toGF216 = (256 * c[0]! + c[1]!).toGF216 := by
  have hg : g.value.val < 65536 := by scalar_tac
  set hi_n := g.value.val / 256
  set lo_n := g.value.val % 256
  have h_hi : hi_n < 256 := Nat.div_lt_of_lt_mul (by omega)
  have h_lo : lo_n < 256 := Nat.mod_lt _ (by omega)
  let hi : U8 := ⟨BitVec.ofNat 8 hi_n⟩
  let lo : U8 := ⟨BitVec.ofNat 8 lo_n⟩
  refine ⟨⟨[hi, lo], by scalar_tac⟩, by simp, ?_⟩
  change g.toGF216 = (256 *hi.val  + lo.val).toGF216
  have h_hi_val : hi.val = hi_n := by
    simp [hi, UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_hi]
  have h_lo_val : lo.val = lo_n := by
    simp [lo, UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lo]
  rw [h_hi_val, h_lo_val]
  change g.value.val.toGF216 = (256 * hi_n + lo_n).toGF216
  congr 1
  omega

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.encode_bytes_base`** (nat-level):

For even-length `msg` with `msg.len ≤ 2^16 * 16`, returns a `PolyEncoder` in `Points` state
with `idx = 0` and every element in `pts[j].value` being a valid big-endian GF(2¹⁶) decode.

Composes `call_once_spec` (empty points) and `loop_spec` (round-robin distribution).

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem encode_bytes_base_spec (msg : Slice U8)
    (h_even : msg.length % 2 = 0)
    (h_len : msg.length ≤ 2 ^ 16 * 16) :
    encode_bytes_base msg ⦃ (result : core.result.Result PolyEncoder
        encoding.EncodingError) =>
      match result with
      | core.result.Result.Ok ⟨idx, EncoderState.Points pts⟩ =>
        idx = 0#u32 ∧
        (∀ (j : Nat), j < 16 →
          ∀ g ∈ pts[j]!.value.val,
            ∃ (c : Slice U8),
              c.length ≥ 2 ∧
              g.toGF216 = (256 * c[0]! + c[1]!).toGF216)
      | _ => False ⦄ := by
  unfold encode_bytes_base
  step*
  case hl =>
    refine core.array.from_fn_loop_const _
      (⟨alloc.vec.Vec.new encoding.gf.GF16⟩ : Point)
      call_mut_ok msg 0#usize (16#usize).val ?_
    simp only [show (16#usize).val = 16 from rfl, show (0#usize : Usize).val = 0 from rfl,
      Nat.zero_add]
    simp only [Usize.max, Usize.numBits]
    cases System.Platform.numBits_eq <;> simp_all
  case hlen =>
    simp only [show (16#usize).val = 16 from rfl, List.length_replicate]
  case hy =>
    cases System.Platform.numBits_eq <;> simp_all
  case hmax =>
    rw [i4_post, i3_post1]
    have h_pow : (1 : Nat) <<< 16 = 65536 := by
      norm_num [Nat.shiftLeft_eq]
    have h_shift : (1 <<< 16) % Usize.size = 65536 := by
      rw [h_pow]
      apply Nat.mod_eq_of_lt
      simp only [Usize.size, Usize.numBits]
      cases System.Platform.numBits_eq <;> simp_all
    rw [h_shift]
    have h_max : (65536 : Nat) * 16 ≤ Usize.max := by
      simp only [Usize.max, Usize.numBits]
      cases System.Platform.numBits_eq <;> simp_all
    omega
  · exfalso
    have h_pow : (1 : Nat) <<< 16 = 65536 := by norm_num [Nat.shiftLeft_eq]
    have h_shift : (1 <<< 16) % Usize.size = 65536 := by
      rw [h_pow]
      apply Nat.mod_eq_of_lt
      simp only [Usize.size, Usize.numBits]
      cases System.Platform.numBits_eq <;> simp_all
    have h_i5 : i5.val = 65536 * 16 := by rw [i5_post, i3_post1, i4_post, h_shift]
    have h_gt' : msg.len.val > i5.val := by scalar_tac
    have h_msglen : msg.len.val = (msg.val).length := by scalar_tac
    grind
  · have h_pts_empty : ∀ (j : Nat), j < 16 → pts.val[j]!.value.val = [] := by
      intro j hj
      rw [pts_post]
      interval_cases j <;> rfl
    have h_msglen : msg.len.val = (msg.val).length := by scalar_tac
    have h_len_bound : (msg.val).length ≤ Usize.max := by
      have h_max : (2 : Nat) ^ 16 * 16 ≤ Usize.max := by
        simp only [Usize.max, Usize.numBits]
        cases System.Platform.numBits_eq <;> simp_all
      grind
    apply WP.spec_bind (core.slice.Slice.chunks_exact_spec msg 2#usize (by decide))
    intro ce h_ce
    obtain ⟨h_ce_len, h_ce_count, _⟩ := h_ce
    simp only [core.slice.iter.IteratorChunksExact.enumerate, bind_tc_ok]
    apply WP.spec_bind
      (encode_bytes_base_loop.loop_spec
        ({ iter := ce, count := 0#usize } :
          core.iter.adapters.enumerate.Enumerate (core.slice.iter.ChunksExact U8))
        pts
        (by grind)
        (by grind)
        (by
          simp only [show (0#usize : Usize).val = 0 from rfl, Nat.zero_add]
          grind))
    intro pts1 h_pts1
    simp only [WP.spec_ok]
    refine ⟨trivial, ?_⟩
    intro j hj g hg
    obtain ⟨suffix, h_suffix_eq, h_suffix_valid⟩ := h_pts1 j hj
    grind

end spqr.encoding.polynomial.PolyEncoder
