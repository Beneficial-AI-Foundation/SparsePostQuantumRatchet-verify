# PR 661 審核：`incremental_mlkem768.rs` 的 top-level spec

分支：`pr-661-review`（merge base `1901a58`）。

Top-level 函數定義：`src/incremental_mlkem768.rs` 中不被同檔案其他函數呼叫的函數。共 5 個：
`generate`、`ek_matches_header`、`encaps1`、`encaps2`、`decaps`。
內部函數（非 top-level）：`potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`、
`flip_endianness_of_encapsulation_state`。

每個 top-level spec 的證明都建立在 `SrcTranslated/FunsExternal.lean` 裡人工撰寫的 libcrux 外部模型上。
Lean 只檢查 theorem 相對於模型成立，不檢查模型相對於 libcrux 成立，因此每節同時列出所依賴的模型。

---

## 1. `generate`

| 項目 | 內容 |
|---|---|
| Rust | `src/incremental_mlkem768.rs:34-43` |
| Lean 檔 | `Spqr/Specs/IncrementalMlkem768/Generate.lean` |
| Theorem | `spqr.incremental_mlkem768.generate_spec` |
| 依賴模型 | `KeyPairCompressedBytes.from_seed`（`FunsExternal.lean:1790`，定義為 `ok { value := keyPairArray (seedOfArray seed) }`）、`pk1`、`pk2`、`sk` |
| FIPS 203 定義 | `Fips203.Bridge.keyPairList`、`pk1Bytes`、`pk2Bytes`（`Bridge/KeyPairBytes.lean`）→ `Fips203.mlkemKeyGen`（Alg 16） |

```lean
theorem generate_spec {R : Type} (rngInst : rand_1.rng.Rng R)
    (cryptoInst : rand_core_1.CryptoRng R) (rng : R)
    (h_fill : ∀ (r : R) (s : Slice Std.U8),
      rngInst.rand_core_1RngCoreInst.fill_bytes r s ⦃ fun _ => True ⦄) :
    generate rngInst cryptoInst rng ⦃ (result : Keys × R) =>
        (∃ seed : Fin 64 → UInt8,
          result.1.dk.val  = Fips203.Bridge.keyPairList seed ∧
          result.1.ek.val  = Fips203.Bridge.toU8List (Fips203.Bridge.pk2Bytes seed) ∧
          result.1.hdr.val = Fips203.Bridge.toU8List (Fips203.Bridge.pk1Bytes seed)) ∧
        result.1.ek.val  = result.1.dk.val.slice mlkem768Params.encapsulationKeyBytes
        (2 * mlkem768Params.encapsulationKeyBytes) ∧
        result.1.hdr.val = result.1.dk.val.slice (2 * mlkem768Params.encapsulationKeyBytes)
        (2 * mlkem768Params.encapsulationKeyBytes + headerBytes) ∧
        result.1.hdr.length = headerBytes ∧
        result.1.ek.length = mlkem768Params.encapsulationKeyBytes ∧
        result.1.dk.length = mlkem768Params.decapsulationKeyBytes ⦄
```

前提：`fill_bytes` 不 panic。
結論：存在 64 byte seed，使 `dk = ML-KEM.KeyGen_internal(seed[0:32], seed[32:64]).dk`
（layout `ByteEncode₁₂(ŝ) ‖ ByteEncode₁₂(t̂) ‖ ρ ‖ H(ek) ‖ z`），`ek = dk[1152:2304]`，`hdr = dk[2304:2368]`，三者長度 2400 / 1152 / 64。

`#print axioms`：`propext, Classical.choice, Quot.sound`。

---

## 2. `ek_matches_header`

| 項目 | 內容 |
|---|---|
| Rust | `src/incremental_mlkem768.rs:28-30` |
| Lean 檔 | `Spqr/Specs/IncrementalMlkem768/EkMatchesHeader.lean` |
| Theorem | `spqr.incremental_mlkem768.ek_matches_header_spec`（`@[step]`） |
| 依賴模型 | `validate_pk_bytes`（`FunsExternal.lean` ~1930，長度檢查 + `Fips203.Bridge.pk2Valid`） |
| FIPS 203 定義 | `Fips203.Bridge.pk2Valid`（`Bridge/EncapsBytes.lean`，`ByteEncode₁₂ ∘ ByteDecode₁₂ = id` 的 modulus check） |

```lean
theorem ek_matches_header_spec (ek hdr : alloc.vec.Vec Std.U8) :
    ek_matches_header ek hdr ⦃ (result : Bool) =>
      let hdrSlice := alloc.vec.Vec.deref hdr
      let ekSlice := alloc.vec.Vec.deref ek
      (hdrSlice.length < 64 → result = false) ∧
      (64 ≤ hdrSlice.length → ekSlice.length < 1152 → result = false) ∧
      (64 ≤ hdrSlice.length → 1152 ≤ ekSlice.length →
        Fips203.Bridge.pk2Valid ekSlice.val → result = true) ∧
      (64 ≤ hdrSlice.length → 1152 ≤ ekSlice.length →
        ¬ Fips203.Bridge.pk2Valid ekSlice.val → result = false) ⦄
```

前提：無。
結論：`result = true` 當且僅當 `hdr.len ≥ 64`、`ek.len ≥ 1152`、`pk2Valid ek`。結論中不出現 `hdr` 的內容。

`#print axioms`：`propext, Classical.choice, Quot.sound`。

---

## 3. `encaps1`

| 項目 | 內容 |
|---|---|
| Rust | `src/incremental_mlkem768.rs:48-66` |
| Lean 檔 | `Spqr/Specs/IncrementalMlkem768/Encaps1.lean` |
| Theorem | `spqr.incremental_mlkem768.encaps1_spec` |
| 依賴模型 | `encapsulate1`（`FunsExternal.lean` ~1975，長度錯誤分支 + `ct1Array` / `overwritePrefix stateOut` / `overwritePrefix ssOut`）、`encaps_state_len`、`SHARED_SECRET_SIZE` |
| FIPS 203 定義 | `Fips203.Bridge.ct1List`、`stateOut`、`ssOut`（`Bridge/EncapsBytes.lean`）→ `Fips203.mlkemEncapsPhase1`（`KEM/EncapsIncremental.lean`，Alg 17 第一輪） |

```lean
theorem encaps1_spec {R : Type} (rngInst : rand_1.rng.Rng R)
    (cryptoInst : rand_core_1.CryptoRng R) (hdr : alloc.vec.Vec Std.U8) (rng : R)
    (h_hdr : 64 ≤ hdr.val.length)
    (h_fill : ∀ (r : R) (s : Slice Std.U8),
      rngInst.rand_core_1RngCoreInst.fill_bytes r s ⦃ fun _ => True ⦄) :
    encaps1 rngInst cryptoInst hdr rng ⦃ (result :
        ((alloc.vec.Vec Std.U8) × (alloc.vec.Vec Std.U8) × (alloc.vec.Vec Std.U8)) × R) =>
      (∃ m : Fin 32 → UInt8,
        result.1.1.val = Fips203.Bridge.ct1List hdr.val h_hdr m ∧
        result.1.2.1.val =
          Fips203.Bridge.toU8List (Fips203.Bridge.stateOut hdr.val h_hdr m) ∧
        result.1.2.2.val =
          Fips203.Bridge.toU8List (Fips203.Bridge.ssOut hdr.val h_hdr m)) ∧
      result.1.1.length = 960 ∧
      result.1.2.1.length = Fips203.Bridge.encapsStateSize ∧
      result.1.2.2.length = Fips203.Bridge.sharedSecretSize ⦄
```

前提：`64 ≤ hdr.len`（Rust 要求 `== 64`，此處較弱）、`fill_bytes` 不 panic。
結論：存在 32 byte 訊息 `m`，使 `(ct1, es, ss)` 分別為 `mlkemEncapsPhase1 (ρ, h) m` 的 `c₁`、序列化 state `ŷ ‖ e₂ ‖ m`、共享密鑰 `K`，其中 `(ρ, h) = (hdr[0:32], hdr[32:64])`。長度 960 / 2080 / 32。

`#print axioms`：`propext, Classical.choice, Quot.sound, Aeneas.Std.core.fmt.Formatter, encaps1._native.decide.ax_1`（後兩者來自 `expect` 的字串）。

---

## 4. `encaps2`

| 項目 | 內容 |
|---|---|
| Rust | `src/incremental_mlkem768.rs:71-79` |
| Lean 檔 | `Spqr/Specs/IncrementalMlkem768/Encaps2.lean` |
| Theorem | `spqr.incremental_mlkem768.encaps2_spec` |
| 依賴模型 | `encapsulate2`（`FunsExternal.lean:1760`，`ok { value := ct2Array state pk2 }`）、`potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`（`FunsExternal.lean:2534`，`fun _es => ok none`）、`tryFromSharedArraySlice_ok_spec` |
| FIPS 203 定義 | `Fips203.Bridge.ct2List`（`Bridge/EncapsBytes.lean`，`decodeEncapsState` + `decodePk2THat`）→ `Fips203.mlkemEncapsPhase2`（Alg 17 第二輪） |

```lean
def encaps2EffectiveState
    (es : alloc.vec.Vec Std.U8) : Result (List Std.U8) := do
  let mf ←
    _root_.incremental_mlkem768.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275
      es
  ok (mf.elim es.val (fun fixed => fixed.val))

def Encaps2Post
    (ek es : alloc.vec.Vec Std.U8)
    (result : alloc.vec.Vec Std.U8) : Prop :=
  ∃ stBytes : List Std.U8,
    encaps2EffectiveState es = ok stBytes ∧
    ∃ (st : Array Std.U8 2080#usize)
      (pk : Array Std.U8 1152#usize),
      st.val = stBytes ∧
      pk.val = ek.val ∧
      result.val = Fips203.Bridge.ct2List st pk

theorem encaps2_spec (ek es : alloc.vec.Vec Std.U8)
    (h_ek : ek.length = 1152) (h_es : es.length = 2080) :
    encaps2 ek es ⦃ (result : alloc.vec.Vec Std.U8) =>
      Encaps2Post ek es result ∧
      result.length = 128 ⦄
```

前提：`ek.len = 1152`、`es.len = 2080`。
結論：`result = ct2List st pk`，其中 `st` 為 endianness workaround 選出的 state、`pk = ek`；長度 128。
證明中 `h_eq : potentially_fix… es = ok none` 直接由模型定義 `simp` 得出，故實際證得的是 `st = es`。

`#print axioms`：`propext, Classical.choice, Quot.sound, Aeneas.Std.core.fmt.Formatter, encaps2._native.decide.ax_2`。

---

## 5. `decaps`

| 項目 | 內容 |
|---|---|
| Rust | `src/incremental_mlkem768.rs:156-169` |
| Lean 檔 | `Spqr/Specs/IncrementalMlkem768/Decaps.lean` |
| Theorem | `spqr.incremental_mlkem768.decaps_spec` |
| 依賴模型 | `decapsulate_compressed_key`（`FunsExternal.lean` ~2040，`ok (ssArray key_pair ct1.value ct2.value)`）、`tryFromSharedArraySlice_ok_spec` |
| FIPS 203 定義 | `Fips203.Bridge.ssList`（`Bridge/DecapsBytes.lean`，`dkOfArray` + `ctOfParts`）→ `Fips203.mlkemDecaps`（`KEM/Decaps.lean`，Alg 18） |

```lean
theorem decaps_spec (dk ct1 ct2 : alloc.vec.Vec Std.U8)
    (h_dk : dk.length = 2400) (h_ct1 : ct1.length = 960) (h_ct2 : ct2.length = 128) :
    decaps dk ct1 ct2 ⦃ (result : alloc.vec.Vec Std.U8) =>
      (∃ (dk' : Array Std.U8 2400#usize) (ct1' : Array Std.U8 960#usize)
          (ct2' : Array Std.U8 128#usize),
        dk'.val = dk.val ∧ ct1'.val = ct1.val ∧ ct2'.val = ct2.val ∧
        result.val = Fips203.Bridge.ssList dk' ct1' ct2') ∧
      result.length = 32 ⦄
```

前提：`dk.len = 2400`、`ct1.len = 960`、`ct2.len = 128`。
結論：`result = ML-KEM.Decaps_internal(dk, ct1 ‖ ct2)`（含 implicit rejection `J(z ‖ c)`）；長度 32。

`#print axioms`：`propext, Classical.choice, Quot.sound, Aeneas.Std.core.fmt.Formatter, encaps2._native.decide.ax_2`。

---

## 串接 top-level spec 的端到端定理

| Theorem | 檔案 | 內容 |
|---|---|---|
| `Fips203.Bridge.ssBytes_roundTrip` | `Bridge/LibcruxDecaps.lean:95` | `ssBytes (keyPairArray seed) (ct1Array …) (ct2Array (stateArray (stateOut …)) (pk2Array (pk2Bytes seed))) = (mlkemEncaps mlkem768 (ekBytes seed) m).ss`，前提 `h_noise`（K-PKE 每係數噪聲 `< ⌊q/4⌋`） |
| `Fips203.Bridge.pk2Valid_pk2Bytes` | `Bridge/EncapsBytes.lean` | `generate` 產生的 `ek` 通過 `pk2Valid` |
| `Fips203.Bridge.ct_eq_ct1Bytes_append_ct2Bytes` | `Bridge/LibcruxEncaps2.lean:116` | `c₁ ‖ c₂` 等於單體 Alg 17 的密文 |

`#print axioms ssBytes_roundTrip`：`propext, Classical.choice, Quot.sound`。

---

## 建置狀態

`lake build` 五個 spec 檔 + `KEM/RoundTrip` + `Bridge/LibcruxDecaps`：通過（2239 jobs，約 2m48s）。
新檔案無 `sorry`、無 `axiom`；hash oracle `hashG`/`hashH`/`hashJ`/`prf`/`xof` 為 `opaque`。
