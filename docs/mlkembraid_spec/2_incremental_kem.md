# Layer 2: Incremental KEM & Erasure Coding (§1.2, §1.3)

> See [README.md](README.md) for extraction status, axiom conventions, and
> the master cross-reference table.

This file covers the cryptographic primitive layer: the incremental KEM
interface (§1.2, §1.2.1) and the chunking/erasure-code layer (§1.3), plus
the GF(2^16) field arithmetic that supports it.

This is the smallest layer by property count but the most axiom-heavy:
KEM roundtrip and SHA3-256 binding must be axiomatised because the
underlying libcrux implementations are opaque.

---

## §1.2 — Incremental KEM Interface

### PROP-3: KEM Roundtrip [ALGEBRAIC SPECIFICATION] 🔶 AXIOM

**Source:** `hax-cross` + `production-test`.

*Given `(dk, ek_seed, ek_vector) = generate(seed)`, the chain
`encaps1` → `encaps2` → `decaps` preserves the shared secret.*

The axiom must explicitly bind `dk`, `ek`, and `hdr` to the same `generate`
call and require `hdr = ek_seed || SHA3-256(ek_seed || ek_vector)`. Without
this binding the axiom can be instantiated with mismatched keys.

**Available in Lean extraction:**

- `incremental_mlkem768.generate` — extracted
- `incremental_mlkem768.encaps1` — extracted
- `incremental_mlkem768.decaps` — extracted
- `incremental_mlkem768.encaps2` — **OPAQUE** (axiom in `FunsExternal.lean`)

**Axiom form:**

```lean
axiom kem_roundtrip (rng_seed : RngSeed) :
    let (dk, ek_seed, ek_vec) := incremental_mlkem768.generate rng_seed
    let hdr := ek_seed ++ sha3_256 (ek_seed ++ ek_vec)
    let ek  := ek_seed ++ ek_vec
    ∀ enc_seed,
      encaps1 hdr enc_seed = ok (es, ct1, ss) →
      encaps2 es ek = ok ct2 →
      decaps dk ct1 ct2 = ok ss
```

| Aspect | Assessment |
|--------|------------|
| **Status** | 🔶 **AXIOM REQUIRED** — `encaps2` opaque |
| **Estimated effort** | 0.5 days (axiom statement with binding) |

**To replace with theorem:** make the `potentially_fix_state*` helper
transparent to Aeneas (it is `#[hax_lib::opaque]` because of `log::*`
macros under `#[cfg(not(hax))]`). Provide a `#[cfg(hax)]` alternative
without logging.

### PROP-3b: EK Header Binding [ALGEBRAIC SPECIFICATION] 🔶 AXIOM

**Source:** `spec-mlkembraid` (§1.2.1).

*`ek_matches_header(ek, hdr)` is equivalent to the spec's
`hdr[32..64] = SHA3-256(hdr[0..32] || ek)`.* The Rust code delegates to
`libcrux_ml_kem::mlkem768::incremental::validate_pk_bytes`, which is opaque.

```lean
axiom ek_matches_header_spec (ek : EncapsulationKey) (hdr : Header) :
    incremental_mlkem768.ek_matches_header ek hdr =
    (hdr[32..64] = sha3_256 (hdr[0..32] ++ ek))
```

| Aspect | Assessment |
|--------|------------|
| **Status** | 🔶 **AXIOM REQUIRED** — `validate_pk_bytes` opaque |
| **Estimated effort** | 0.5 days |

---

## §1.3 — Chunking with Erasure Codes

### LEAN-ENC-1: Point Serialize/Deserialize Roundtrip ✅ PROVED

**Source:** `lean-specific`.

*`deserialize(serialize(pt)) = ok pt`* for the `Pt` type used in
Reed-Solomon encoding points.

**Proof files:**

- `Spqr/Specs/Encoding/Polynomial/Pt/Serialize.lean` — `serialize_spec`,
  `to_be_bytes_spec`
- `Spqr/Specs/Encoding/Polynomial/Pt/Deserialize.lean` — `deserialize_spec`,
  `from_be_bytes_spec`, `try_from_spec`

### LEAN-ENC-2: PolyDecoder Full Decode [BLOCKED] 🚫

**Source:** `lean-specific`.

*Given any `N` distinct chunks for a message of length fitting in `N`
codewords, `decoded_message` returns the original message.*

| Aspect | Assessment |
|--------|------------|
| **Blocker** | `PolyDecoder::decoded_message` is opaque (via `aeneas-config.yml`). The full erasure-code roundtrip cannot be proved without an axiom for `decoded_message`. |
| **Additional blockers** | 4 sorry'd loop bodies in `Funs.lean` (`parallel_mult_loop`, `lagrange_polys_for_complete_points_loop0`, `PolyEncoder::from_pb_loop1`, `PolyEncoder::encode_bytes_base_loop`) |
| **Status** | 🚫 **BLOCKED** |
| **Estimated effort** | 2–3 days (after opacity lifted) |

---

## GF(2^16) Field Arithmetic

These properties connect the extracted GF16 operations to Mathlib's
`GaloisField 2 16` (`abbrev GF216 := GaloisField 2 16` in
`Spqr/Math/Basic.lean`). They support the erasure-coding layer.

### LEAN-GF-1: GF16 Addition (AddAssign) ✅ PROVED

`add_assign_spec`: `GF16::add_assign(a, b).value = a.value + b.value` in GF(2^16).

**Proof file:** `Spqr/Specs/Encoding/Gf/GF16/AddAssign.lean`

### LEAN-GF-2: GF16 Addition (by Value) ✅ PROVED

`add_spec` in `Spqr/Specs/Encoding/Gf/GF16/Add.lean`.

### LEAN-GF-3: GF16 Subtraction ✅ PROVED

`sub_spec`: GF(2^16) subtraction = addition (XOR).

**Proof file:** `Spqr/Specs/Encoding/Gf/GF16/Sub.lean`

### LEAN-GF-4: GF16 Equality ✅ PROVED

`eq_spec` + `gf16_eq_iff` in `Spqr/Specs/Encoding/Gf/GF16/Eq.lean`.

### LEAN-GF-5: GF16 Carry-Less Multiplication Loop ✅ PROVED

`poly_mul_loop_spec`, `poly_mul_spec`, `poly_mul_spec'`, `clmul_eq_clmul_poly`,
`clmul_poly_eq_mul` in `Spqr/Specs/Encoding/Gf/Unaccelerated/PolyMul.lean`.

Connects the bit-level loop to polynomial multiplication in `(ZMod 2)[X]`
using Mathlib's polynomial ring theory.

### LEAN-GF-6: GF16 Polynomial Reduction [PARTIAL] ⚠️

**Status:** ⚠️ **PARTIAL** — 1 sorry remains.

- `poly_reduce_poly_mul_spec` — **sorry**

The mathematical framework is in place (definitions of `polyMod`,
`reduceFromByte`, `POLY_GF2`, `polyMod_poly`). The remaining work is
connecting the precomputed `REDUCE_BYTES` table to the recursive spec.

**Proof file:** `Spqr/Specs/Encoding/Gf/Reduce/PolyReduce.lean`

### LEAN-GF-7: GF16 Multiplication End-to-End [PARTIAL] ⚠️

**Status:** ⚠️ **PARTIAL** — 2 sorries remain (`mul_spec'`, `mul_spec`),
blocked on LEAN-GF-6.

**Proof file:** `Spqr/Specs/Encoding/Gf/Unaccelerated/Mul.lean`

**Path to close:**

1. Connect `REDUCE_BYTES` table to `reduceFromByte` (concrete computation).
2. Prove `polyMod_poly p n = p %ₘ POLY_GF2` using Mathlib.
3. Prove `polyMod_eq_polyMod_poly` by induction on `n`.
4. Compose to get `mul_spec` from `poly_mul_spec` + `poly_reduce_spec`.
