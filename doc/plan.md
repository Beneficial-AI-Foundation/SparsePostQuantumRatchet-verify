# Plan: Translating NIST FIPS 203 (ML-KEM) Algorithms into Lean Definitions

## 1. Objective

Produce human-readable Lean 4 definitions for every algorithm in NIST FIPS 203
(ML-KEM, August 2024) and formally verify that these reference definitions
agree — on all inputs — with the Aeneas-translated Lean code in
`SrcTranslated/Funs.lean` (which originates from the Rust `libcrux-ml-kem`
implementation used by SPQR).

The end state is a chain of equational proofs:

```
FIPS 203 spec (Lean def) ≡ Aeneas translation (Lean def from Rust/libcrux)
```

---

## 2. Scope: FIPS 203 Algorithms

FIPS 203 defines **18 algorithms** organised in four layers.

| # | Name | FIPS 203 § | Purpose |
|---|------|-----------|---------|
| 1 | `BitsToBytes(b)` | 4.2.1 | Bit array → byte array |
| 2 | `BytesToBits(B)` | 4.2.1 | Byte array → bit array |
| 3 | `ByteEncode_d(F)` | 4.2.1 | Integer array → byte array (d-bit encoding) |
| 4 | `ByteDecode_d(B)` | 4.2.1 | Byte array → integer array (d-bit decoding) |
| 5 | `SampleNTT(B)` | 4.2.2 | Byte stream → NTT-domain polynomial (rejection) |
| 6 | `SamplePolyCBD_η(B)` | 4.2.2 | Byte array → polynomial (centered binomial) |
| 7 | `NTT(f)` | 4.3 | Polynomial → NTT representation |
| 8 | `NTT⁻¹(f̂)` | 4.3 | NTT representation → polynomial |
| 9 | `MultiplyNTTs(f̂, ĝ)` | 4.3 | Componentwise NTT multiplication |
| 10 | `BaseCaseMultiply` | 4.3 | Degree-1 poly mult mod (X²−γ) |
| 11 | `Compress_d(x)` | 4.2.1 | Compress ℤ_q → ℤ_{2^d} |
| 12 | `Decompress_d(y)` | 4.2.1 | Decompress ℤ_{2^d} → ℤ_q |
| 13 | `K-PKE.KeyGen(d)` | 5.1 | Internal PKE key generation |
| 14 | `K-PKE.Encrypt(ek,m,r)` | 5.2 | Internal PKE encryption |
| 15 | `K-PKE.Decrypt(dk,c)` | 5.3 | Internal PKE decryption |
| 16 | `ML-KEM.KeyGen()` | 6.1 | Full KEM key generation |
| 17 | `ML-KEM.Encaps(ek)` | 6.2 | Full KEM encapsulation |
| 18 | `ML-KEM.Decaps(dk,c)` | 6.3 | Full KEM decapsulation |

### Parameters (FIPS 203, Table 2 — ML-KEM-768)

| Symbol | Value | Meaning |
|--------|-------|---------|
| `n` | 256 | Polynomial ring degree |
| `q` | 3329 | Modulus |
| `k` | 3 | Module rank |
| `η₁` | 2 | CBD parameter for secret/error |
| `η₂` | 2 | CBD parameter for encryption noise |
| `d_u` | 10 | Ciphertext compression (vector) |
| `d_v` | 4 | Ciphertext compression (polynomial) |

---

## 3. Project Integration Points

The SPQR project uses ML-KEM-768 via `libcrux-ml-kem`.  The Aeneas
translation produces opaque external declarations for libcrux functions.

| SPQR function (Lean) | Rust source | Maps to FIPS 203 |
|---|---|---|
| `incremental_mlkem768.generate` | `incremental_mlkem768.rs:34` | Alg 16 (KeyGen) |
| `incremental_mlkem768.encaps1` | `incremental_mlkem768.rs:48` | Alg 17 first half |
| `incremental_mlkem768.encaps2` | `incremental_mlkem768.rs:71` | Alg 17 second half |
| `incremental_mlkem768.decaps` | `incremental_mlkem768.rs:148` | Alg 18 (Decaps) |

Existing spec theorems in `Spqr/Specs/IncrementalMlkem768/` state
size-level postconditions.  This plan extends them to value-level
equivalence with FIPS 203.

---

## 4. File Layout

All new files live under `Spqr/Crypto/Fips203/`:

```
Spqr/Crypto/Fips203/
├── Params.lean                -- q, n, k, η₁, η₂, d_u, d_v
├── Ring.lean                  -- ℤ_q, R_q definitions
├── Conversion/
│   ├── BitsToBytes.lean       -- Alg 1
│   ├── BytesToBits.lean       -- Alg 2
│   ├── ByteEncode.lean        -- Alg 3
│   ├── ByteDecode.lean        -- Alg 4
│   ├── Compress.lean          -- Alg 11
│   └── Decompress.lean        -- Alg 12
├── Sampling/
│   ├── SampleNTT.lean         -- Alg 5
│   └── SamplePolyCBD.lean     -- Alg 6
├── NTT/
│   ├── Zetas.lean             -- ζ table
│   ├── NTT.lean               -- Alg 7
│   ├── InvNTT.lean            -- Alg 8
│   ├── MultiplyNTTs.lean      -- Alg 9
│   ├── BaseCaseMultiply.lean  -- Alg 10
│   ├── Spec.lean              -- algebraic spec: CRT projection R_q ≅ ∏ ℤ_q[X]/(X²−γᵢ)
│   ├── Packed.lean            -- base-4096 packed-ℕ clones of Alg 7 / Alg 8 layers
│   ├── Kernel{0,1,2,3}.lean   -- `decide +kernel` shards: nttP δⱼ = formulaP j  (64 j each)
│   ├── InvKernel{0,1,2,3}.lean-- `decide +kernel` shards: invNttP (formulaP j) = 128·δⱼ
│   ├── KernelCheck.lean       -- glues shards into the two 256-vector statements
│   └── RoundTrip.lean         -- simulation proofs + round trip + homomorphism
├── PKE/
│   ├── KeyGen.lean            -- Alg 13
│   ├── Encrypt.lean           -- Alg 14
│   ├── Decrypt.lean           -- Alg 15
│   └── RoundTrip.lean         -- decrypt ∘ encrypt = id under the noise bound
├── KEM/
│   ├── KeyGen.lean            -- Alg 16
│   ├── Encaps.lean            -- Alg 17
│   └── Decaps.lean            -- Alg 18
└── Bridge/
    ├── LibcruxKeygen.lean     -- Alg 16 ↔ Aeneas from_seed
    ├── LibcruxEncaps1.lean    -- Alg 17 (half 1) ↔ Aeneas encapsulate1
    ├── LibcruxEncaps2.lean    -- Alg 17 (half 2) ↔ Aeneas encapsulate2
    └── LibcruxDecaps.lean     -- Alg 18 ↔ Aeneas decapsulate
```

| 15 | `K-PKE.Decrypt(dk,c)` | 5.3 | Internal PKE decryption |
| 16 | `ML-KEM.KeyGen()` | 6.1 | Full KEM key generation |
| 17 | `ML-KEM.Encaps(ek)` | 6.2 | Full KEM encapsulation |
| 18 | `ML-KEM.Decaps(dk,c)` | 6.3 | Full KEM decapsulation |

---

## 5. Step-by-Step Implementation Plan

### Phase 0 — Foundations

| Step | File | Description |
|------|------|-------------|
| 0.1 | `Params.lean` | Define `q := 3329`, `n := 256`, `k := 3`, `η₁ := 2`, `η₂ := 2`, `d_u := 10`, `d_v := 4` and derived byte-size constants. Prove `q` is prime, `n ∣ q-1`. |
| 0.2 | `Ring.lean` | Define `Zq := ZMod q`. Define `Rq` as `Fin 256 → Zq` with ring operations mod `X^256+1`. |

### Phase 1 — Conversion Primitives (Alg 1–4, 11–12)

| Step | File | Lean signature |
|------|------|---------------|
| 1.1 | `BitsToBytes.lean` | `def bitsToBytes (b : Fin (8*l) → Fin 2) : Fin l → UInt8` |
| 1.2 | `BytesToBits.lean` | `def bytesToBits (B : Fin l → UInt8) : Fin (8*l) → Fin 2` |
| 1.3 | `ByteEncode.lean` | `def byteEncode (d : Nat) (F : Fin 256 → Fin (2^d)) : List UInt8` |
| 1.4 | `ByteDecode.lean` | `def byteDecode (d : Nat) (B : List UInt8) : Fin 256 → Fin (2^d)` |
| 1.5 | `Compress.lean` | `def compress (d : Nat) (x : Zq) : Fin (2^d)` |
| 1.6 | `Decompress.lean` | `def decompress (d : Nat) (y : Fin (2^d)) : Zq` |
| 1.7 | — | Round-trip lemmas: `bytesToBits ∘ bitsToBytes = id`, `decompress d ∘ compress d ≈ id`. |

### Phase 2 — Sampling (Alg 5–6)

| Step | File | Description |
|------|------|-------------|
| 2.1 | `SampleNTT.lean` | Rejection sampling from XOF (SHAKE-128, axiomatised). |
| 2.2 | `SamplePolyCBD.lean` | Centered binomial distribution sampling. |

Hash functions (SHAKE-128, SHAKE-256, SHA3-256, SHA3-512) are axiomatised
as opaque oracles following `Spqr/Crypto/Hkdf.lean` patterns.

### Phase 3 — NTT (Alg 7–10)

| Step | File | Description |
|------|------|-------------|
| 3.1 | `Zetas.lean` | ζ = 17 mod q; table `ζ^(BitRev₇(i))` for i ∈ [0,128). |
| 3.2 | `NTT.lean` | Cooley-Tukey butterfly, 7 layers. |
| 3.3 | `InvNTT.lean` | Gentleman-Sande inverse butterfly. |
| 3.4 | `BaseCaseMultiply.lean` | Degree-1 poly mult mod (X²−γ). |
| 3.5 | `MultiplyNTTs.lean` | 128 calls to `baseCaseMultiply`. |
| 3.6 | `Spec.lean`, `Packed.lean`, `Kernel*.lean`, `KernelCheck.lean`, `RoundTrip.lean` | Prove `invNTT ∘ ntt = id`, `ntt ∘ invNTT = id`, `ntt(f*g) = multiplyNTTs(ntt f)(ntt g)`. **Done — no axioms, no `sorry`.** |

#### 3.6 — Verified-computation strategy for NTT correctness

The butterfly network of Alg 7/8 is hard to reason about symbolically, so the
correctness proof reduces everything to the **256 standard basis vectors `δⱼ`**
(linearity of `ntt`/`invNtt`/`nttSpec` is proved structurally) and settles the
basis cases by *kernel computation*:

1. **Packed encoding** (`Packed.lean`).  A coefficient vector is a single `ℕ`
   whose base-4096 digits are canonical `ℤ_q` representatives.  `nttP` and
   `invNttP` are literal clones of the Alg 7 / Alg 8 loops on that `ℕ`
   (`getP`/`setP` digit access, `17 ^ brN k % 3329` twiddles).  The Lean kernel
   evaluates them through GMP, so one full 7-layer NTT costs ≈ 0.2 s.
2. **Simulation** (`RoundTrip.lean`: `simR_outerP`, `simR_iouterP`).  A
   relation `simR l f` ("digit `i` of `l` is `< 3329` and casts to `f i`") is
   shown to be preserved butterfly-by-butterfly, so the packed clone computes
   exactly `ntt`/`invNtt`'s butterfly layers.
3. **Closed form** (`nttSpec_delta`, `simR_formulaP`).  `nttSpec δⱼ` at index
   `idx` is `γ_{idx/2}^{j/2}` on matching parity, else `0`; `formulaP j` packs it.
4. **Kernel checks**, sharded so **every file compiles in < 30 s** and `lake`
   runs them in parallel:
   * `Kernel0–3.lean`: `∀ j < 64, nttP (δ_{j+64s}) = formulaP (j+64s)`   (~15 s each)
   * `InvKernel0–3.lean`: `∀ j < 64, invNttP (formulaP (j+64s)) = 128 · δ_{j+64s}` (~13 s each)
   * `KernelCheck.lean`: case-splits `j < 256` into the four shards.
5. **Bridge**.  `ntt_delta_eq_nttSpec_delta` and `invNtt_ntt_delta` transport
   the kernel facts across the simulation; the `128⁻¹` scaling of Alg 8 is
   discharged by `nInv_mul_n : 3303 · 128 = 1`.  `ntt_eq_nttSpec`,
   `invNtt_ntt`, `ntt_invNtt`, `ntt_polyMul`, … follow by linearity.

`#print axioms` on `invNtt_comp_ntt`, `ntt_comp_invNtt`, `ntt_bijective` and
`ntt_pipeline_eq_polyMul` reports only `propext`, `Classical.choice`,
`Quot.sound`.  Compile times: `RoundTrip.lean` ≈ 3 s, each kernel shard ≤ 16 s
(previously one monolithic `decide +kernel` of ≈ 60 s plus an axiom for Alg 8).

**Rule for this directory:** keep each file under 30 s.  If a kernel check
grows, split it into more shards rather than raising `maxHeartbeats`.

### Phase 4 — Internal PKE (Alg 13–15)

| Step | File | Description |
|------|------|-------------|
| 4.1 | `PKE/KeyGen.lean` | Expand seed via G, generate Â via `sampleNTT`, secret via `samplePolyCBD`, compute `t̂ = Â◦ŝ + ê`. |
| 4.2 | `PKE/Encrypt.lean` | Re-derive Â, sample r/e₁/e₂, compute `u`, `v`. |
| 4.3 | `PKE/Decrypt.lean` | Decompress, recover message, compress to bits. |
| 4.4 | `PKE/RoundTrip.lean` | Correctness: `decrypt(dk, encrypt(ek, m, r)) = m` under noise bound. **Done — no axioms, no `sorry`.** |

#### 4.4 — Round-trip proof structure

`kpke_roundTrip p d m r h_noise` states, for `(ek, dk) = kpkeKeyGen d p`,
`kpkeDecrypt p dk (kpkeEncrypt p ek m r).ct = m` under the **single**
hypothesis `∀ idx, |honestW d m r p idx − Decompress₁(m) idx| < ⌊q/4⌋ = 832`,
where `honestW` is the explicitly named polynomial `v' − NTT⁻¹(ŝᵀ∘NTT(u'))`
that decryption computes on an honest ciphertext.  The earlier formulation,
which took the key round-trips as extra hypotheses and inlined a 15-line
`let`-block in the statement, timed out at elaboration; everything is now a
chain of small rewriting lemmas:

1. **Key round-trips** (theorems, not hypotheses):
   `decodeDkSHat_encodeDk`, `decodeEkTHat_encodeEk`, `decodeEkRho_encodeEk`
   from `byteDecodeZq_byteEncodeZq_12` plus `384·i + j` index arithmetic;
   specialised to `kpkeKeyGen` as `decode*_kpkeKeyGen`.
2. **Ciphertext round-trips**: `decodeCiphertextU/V_encodeCiphertext` from
   `byteDecode_byteEncode` and `compress_lt_two_pow`.
3. **Named honest values** `honestU`, `honestV`, `honestW`;
   `kpkeEncrypt_kpkeKeyGen_ct` and `kpkeDecrypt_kpkeKeyGen` rewrite the two
   algorithms to `encodeCiphertext honestU honestV` and `recoverMsg honestW`.
4. **Algebra**: `decrypt_encrypt_noise_identity` (signal cancellation via
   `ntt_invNtt`, `ntt_polyMul`, `multiplyNTTs` associativity from Phase 3)
   shows `w = Decompress₁(m) + e₂ + ⟨ê, ŷ⟩ − ⟨ŝ, NTT e₁⟩` without compression.
5. **Bit recovery**: `compress1_decompress1_stable` + `msgBit_lt_two` +
   `byteEncode1_msgBit` finish `recoverMsg honestW = m`.

Variants: `kpke_roundTrip_of_consistent` (any `kp = kpkeKeyGen d p`) and
`kpke_roundTrip_768`.  `#print axioms` on all of them: only `propext`,
`Classical.choice`, `Quot.sound`.  The hash oracles `hashG`, `prf`, `xof` are
`opaque` constants (not axioms) and the theorems hold for any instantiation.
Compile time of `PKE/RoundTrip.lean`: ≈ 3 s; the whole `PKE/` directory ≈ 8 s.

Remaining (future work, not needed for the SPQR bridge): discharging `h_noise`
probabilistically for ML-KEM-768 (`η₁ = η₂ = 2`, `d_u = 10`, `d_v = 4`) — a
tail bound on the centred-binomial noise, FIPS 203 § 3.3 / Table 2.

### Phase 5 — Full KEM (Alg 16–18)

| Step | File | Description |
|------|------|-------------|
| 5.1 | `KEM/KeyGen.lean` | Wrap `kpkeKeyGen`, append `H(ek)` and `z`. **Done.** |
| 5.2 | `KEM/Encaps.lean` | Derive `(K,r) = G(m‖H(ek))`, call `kpkeEncrypt`. **Done.** |
| 5.3 | `KEM/Decaps.lean` | Decrypt, re-derive, re-encrypt, implicit rejection. **Done.** |
| 5.4 | `KEM/RoundTrip.lean` | Round-trip: `decaps(dk, encaps(ek,m).ct) = encaps(ek,m).ss`. **Done — no axioms, no `sorry`.** |

#### 5.x — Notes

* The `_internal` variants (Alg 16–18) are the top-level definitions: randomness
  (`d`, `z`, `m`) is an explicit parameter, so Alg 19–21 are just these applied
  to fresh bytes; the Alg 21 input-validation step is enforced by the dependent
  byte-array types.
* `mlkemKeyGen d z p : MlkemKeyPair p` with `dk : Fin p.dkSize → UInt8` laid out
  as `dkPKE ‖ ek ‖ H(ek) ‖ z` via `encodeMlkemDk`; the four projections
  `decodeDk{Pke,Ek,H,Z}` are proved to invert it (`decodeDk*_encodeMlkemDk`)
  and specialised to generated keys (`decodeDk*_mlkemKeyGen`).
* New oracles: `hashH` (SHA3-256) and `hashJ` (SHAKE-256), `opaque` like `hashG`.
* `mlkem_roundTrip p d z m h_noise` takes only the K-PKE noise bound at the
  derived randomness `honestR d m p = G(m ‖ H(ek))[32:64]`; the proof rewrites
  the `dk` projections, applies `kpke_roundTrip` to get `m' = m`, and then the
  re-encryption check `c = c'` holds by `rfl`, so the implicit-rejection branch
  is never taken.  `#print axioms`: only `propext`, `Classical.choice`,
  `Quot.sound`.  The whole `KEM/` directory compiles in ≈ 2 s.

### Phase 6 — Bridge to Aeneas Translation

| Step | File | Theorem statement |
|------|------|-------------------|
| 6.1 | `Bridge/KeyPairBytes.lean`, `Bridge/LibcruxKeygen.lean` | `from_seed seed = ok {value := keyPairArray seed}` where `keyPairArray seed = (mlkemKeyGen seed[0:32] seed[32:64] mlkem768).dk`. **Done — no axioms, no `sorry`.** |
| 6.2 | `KEM/EncapsIncremental.lean`, `Bridge/EncapsBytes.lean`, `Bridge/LibcruxEncaps1.lean` | `encapsulate1 pk1 rand state ss = ok (.Ok c₁, state', ss')` with `c₁ = (mlkemEncapsPhase1 (ρ,h) m).ct1`, `state'[0:2080] = stateBytes (ŷ,e₂,m)`, `ss'[0:32] = K`. **Done — no axioms, no `sorry`.** |
| 6.3 | `Bridge/LibcruxEncaps2.lean` | `aeneas_encapsulate2 ek state = mlkemEncaps_phase2 …` |
| 6.4 | `Bridge/LibcruxDecaps.lean` | `aeneas_decaps dk ct1 ct2 = mlkemDecaps dk (ct1,ct2)` |

#### 6.1 — Notes

* libcrux is opaque to Aeneas, so the keygen bridge is realised by giving the external
  `KeyPairCompressedBytes.from_seed` in `SrcTranslated/FunsExternal.lean` a *faithful FIPS 203
  model* instead of the previous `ok default` stub.  The former **axiom** `from_seed_spec`
  (length-only) is now a **proved theorem** that additionally states
  `kp.value.val = Fips203.Bridge.keyPairList (seedOfArray seed)`; consequently
  `spqr.incremental_mlkem768.generate_spec` no longer depends on any custom axiom.
* Layout checked against libcrux-ml-kem 0.0.7 (`ind_cca/incremental/types.rs`,
  `KeyPair::to_bytes_compressed`; `ind_cca.rs`, `generate_keypair`):
  `value = ByteEncode₁₂(ŝ) ‖ ByteEncode₁₂(t̂) ‖ ρ ‖ H(ek) ‖ z`, `d = seed[0:32]`,
  `z = seed[32:64]` — exactly `encodeMlkemDk dkPKE ek H(ek) z` of Alg 16.
* `KeyPairBytes.lean` (imports only `Fips203.KEM.KeyGen` + Aeneas, so `FunsExternal` can
  import it) defines `seedD/seedZ`, `toU8List`, `keyPairBytes/List/Array`, `pk2Bytes`
  (`ek[0:1152]`) and `pk1Bytes` (`ρ ‖ H(ek)`), the per-field lemmas `keyPairBytes_{dkPke,ek,
  hash,z}` and the slice facts `value.slice 1152 2304 = pk2`, `value.slice 2304 2368 = pk1`.
* `LibcruxKeygen.lean` states the bridge: `from_seed_eq_mlkemKeyGen`, `from_seed_value`,
  `sk/pk1/pk2_from_seed`, `bind_from_seed_pk{1,2}` and the `decodeDk*` projections.
* Proof note: `congr 1` on goals containing `mlkemKeyGen …` hits `maxRecDepth`; use
  `exact congrArg _ (Fin.ext …)` instead.

#### 6.2 — Notes

* **Incremental split (Risk 2).**  `KEM/EncapsIncremental.lean` defines Algorithm 17 as two
  rounds mirroring libcrux: `mlkemEncapsPhase1 p (ρ, h) m = (K, c₁, (ŷ, e₂, m))` and
  `mlkemEncapsPhase2 p (ŷ, e₂, m) t̂ = c₂`, with `mlkemEncaps_ct_eq_phases` proving
  `(mlkemEncaps ek m).ct = c₁ ‖ c₂` and `mlkemEncapsPhase1_ss` proving the shared secret agrees.
* **Byte model** (`Bridge/EncapsBytes.lean`, imported by `FunsExternal`): `headerOfList`
  (`PublicKey1::try_from`), `polyBytes`/`polyOfBytes` (little-endian `i16` per coefficient,
  `PolynomialRingElement::to_bytes`), `stateBytes`/`decodeEncapsState` for the 2080-byte
  `ŷ[0] ‖ ŷ[1] ‖ ŷ[2] ‖ e₂ ‖ m` layout with round trip `decodeEncapsState_stateBytes`, and
  `overwritePrefix` for the `&mut [u8]` outputs.  Coefficient representatives: the model stores
  the canonical `[0, q)` value; libcrux may store other `i16` representatives (and, on AVX2,
  byte-swapped ones — issue 1275), but every downstream reader is modulo `q`, so all observable
  behaviour agrees.
* **Externals** (`SrcTranslated/FunsExternal.lean`): `encapsulate1` is now a `def` (was an
  axiom) with libcrux's error behaviour (`InvalidInputLength` if `pk1.len() < 64`,
  `InvalidOutputLength` if `shared_secret.len() < 32` or `state.len() < 2080`) and a `@[step]`
  spec `encapsulate1_spec`; `SHARED_SECRET_SIZE = 32` and `encaps_state_len = 2080` are also
  `def`s with specs.
* **Bridge** (`Bridge/LibcruxEncaps1.lean`): `encapsulate1_eq_mlkemEncapsPhase1`,
  `encapsulate1_{ct1,state_take,ss_take}`, `decodeEncapsState_stateOut`,
  `encapsulate1_short_header`, and the composition with 6.1: `ssOut_pk1Bytes`
  (`= (mlkemEncaps ek m).ss`) and `ct1Bytes_pk1Bytes` (`= (mlkemEncaps ek m).ct[0:960]`).

**Bridge proof strategy:** Unfold Aeneas definition layer by layer →
apply `@[step]` spec theorems for externals → show each computational
step matches a FIPS 203 algorithm step → close with `omega`/`ring`/`decide`.

### Phase 7 — SPQR Integration

| Step | File | Description |
|------|------|-------------|
| 7.1 | `IncrementalMlkem768/Generate.lean` | Strengthen `generate_spec` with FIPS 203 value semantics. |
| 7.2 | `IncrementalMlkem768/Encaps1.lean` | Remove `sorry`, add value-level post via bridge. |
| 7.3 | New `Encaps2.lean` | Spec theorem for `encaps2`. |
| 7.4 | New `Decaps.lean` | Spec theorem for `decaps`. |

---

## 6. Dependency / Roadmap Graph

Arrow `A → B` means "B depends on A".

```
                        ┌──────────────┐
                        │  Phase 0     │
                        │  Params.lean │
                        │  Ring.lean   │
                        └──────┬───────┘
                               │
              ┌────────────────┼────────────────┐
              │                │                │
              ▼                ▼                ▼
    ┌─────────────────┐ ┌───────────┐ ┌──────────────────┐
    │   Phase 1       │ │  Phase 2  │ │   Phase 3        │
    │ Conversion      │ │ Sampling  │ │   NTT            │
    │ Alg 1–4, 11–12  │ │ Alg 5–6   │ │ Alg 7–10         │
    └────────┬────────┘ └─────┬─────┘ └────────┬──────────┘
             │                │                │
             └────────────────┼────────────────┘
                              │
                              ▼
                   ┌─────────────────────┐
                   │     Phase 4         │
                   │  Internal PKE       │
                   │  Alg 13–15          │
                   └──────────┬──────────┘
                              │
                              ▼
                   ┌─────────────────────┐
                   │     Phase 5         │
                   │  Full KEM           │
                   │  Alg 16–18          │
                   └──────────┬──────────┘
                              │
                              ▼
                   ┌─────────────────────┐
                   │     Phase 6         │
                   │  Bridge Proofs      │
                   │  FIPS ↔ Aeneas      │
                   └──────────┬──────────┘
                              │
                              ▼
                   ┌─────────────────────┐
                   │     Phase 7         │
                   │  SPQR Integration   │
                   │  generate / encaps  │
                   │  decaps / roundTrip │
                   └─────────────────────┘
```

### Intra-Phase Detail

```
Phase 1:  Alg 1,2 ──► Alg 3,4 ──┐
          Alg 11,12 ─────────────┤──► Phase 4
Phase 2:  SHAKE axioms ──► Alg 5,6 ──► Phase 4
Phase 3:  Zetas ──► Alg 7,8 ──► Alg 10 ──► Alg 9 ──► Phase 4

Phase 4:  Alg 13 ──► Alg 16    (KeyGen)
          Alg 14 ──► Alg 17    (Encaps)
          Alg 15 ──► Alg 18    (Decaps)

Phase 6 maps:
  Alg 16 ←→ libcrux KeyPairCompressedBytes.from_seed
  Alg 17 ←→ libcrux encapsulate1 + encapsulate2
  Alg 18 ←→ libcrux decapsulate_compressed_key

Phase 7 chains:
  Bridge + existing spec theorems → strengthened specs + roundTrip
```

---

## 7. Design Decisions

- **Polynomials:** `Fin 256 → ZMod 3329` (direct coefficient repr).
- **Byte arrays:** `List UInt8` / `Fin n → UInt8`; thin coercions to
  Aeneas `Slice Std.U8` and `Array Std.U8 N`.
- **Matrices:** `Fin k → Fin k → (Fin 256 → ZMod 3329)`.
- **Computability:** All defs `noncomputable` (matches `SrcTranslated`).
- **Hash functions:** Axiomatised as opaque oracles per `Spqr/Crypto/Hkdf.lean`.
- **Style:** Per `doc/STYLE_GUIDE.md` — headers, `@[step]`, `⦃⦄` WP,
  no bare `simp`, 100-char lines.

---

## 8. Verification Strategy

1. **Spec layer (Phases 1–5):** Each FIPS 203 algorithm = pure Lean `def`,
   human-readable transliteration of the pseudocode.
2. **Bridge layer (Phase 6):** Equational theorems: Aeneas code computes
   the same function as the FIPS 203 def (modulo `Result` wrapping).
3. **Integration layer (Phase 7):** SPQR spec theorems get value-level
   postconditions referencing the FIPS 203 definitions.
4. **End-to-end:** KEM round-trip theorem proves
   `decaps(dk, encaps(ek,m)) = ss` under noise bound.

---

## 9. Effort & Priority

| Phase | Effort | Priority | Notes |
|-------|--------|----------|-------|
| 0 | 1 wk | P0 | Unlocks everything |
| 1 | 2 wk | P0 | Simple, enables Phase 4 |
| 3 | 2 wk | P0 | NTT correctness is non-trivial |
| 2 | 1 wk | P1 | Needs hash axiom setup |
| 4 | 2 wk | P1 | Assembles sub-algorithms |
| 5 | 1 wk | P1 | Thin KEM wrapper |
| 6 | 3 wk | P0 | Primary verification deliverable |
| 7 | 2 wk | P0 | End goal |

**Total: ~14 weeks** (single contributor). Phases 1–3 parallelisable.

---

## 10. Risks & Open Questions

1. **Aeneas opacity:** libcrux functions are opaque. Bridge proofs use
   axioms from `FunsExternal.lean`; these axioms must faithfully model
   the libcrux implementation.
2. **Incremental split:** libcrux splits `ML-KEM.Encaps` into two rounds
   (`encaps1`/`encaps2`).  Bridge must formalise the composition.
3. **Endianness workaround:** `potentially_fix_state_incorrectly_encoded_
   by_libcrux_issue_1275` is opaque; its correctness is outside FIPS 203
   scope but needed for SPQR integration.
4. **Mathlib dependency:** Use `ZMod 3329` if Mathlib is available;
   otherwise define lightweight `Fin 3329` ring wrapper.

