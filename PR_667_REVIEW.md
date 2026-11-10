# PR 667 審核：`From<Direction> for i32` spec + `init_inner` spec

分支：`pr-667-review`（merge base `236adcc1`，即 origin/main HEAD）。
變更：`Spqr.lean`（+2 import）、`Spqr/Specs/Proto/PqRatchet/Direction/From.lean`（新）、
`Spqr/Specs/Lib/InitInner.lean`（新）。

驗證：`lake build` 兩模組通過、`lake exe runLinter` 兩模組通過、CI 三項全綠、無 sorry。

## 結論：可合併，有幾個小修正建議

### `Direction/From.lean` — OK
- 後置條件 `A2B ↦ 0, B2A ↦ 1` 與 `src/proto/pq_ratchet.proto:218-221`（`A_2_B = 0; B_2_A = 1`）一致。
- `#print axioms`：僅 propext / Classical.choice / Quot.sound。

### `InitInner.lean` — 可合併，建議修正
- `InitInner.lean:61`、`:94`、`:135`：裸 `simp` / `simpa [...]`，違反 STYLE_GUIDE「用 `simp only`」規則，且無說明註解（linter 未攔）。
- `InitInner.lean:80`：`init_inner_spec_v1_a2b` 沒有 `@[step]`，而 `_v0`、`_v1_b2a`、`_v1` 都有。不一致；要嘛 a2b 也加，要嘛 b2a 也拿掉（`_v1` 已足以給 `step*` 用）。
- `InitInner.lean:172`：docstring 提到 `initial_state_spec_v1`，repo 中不存在此 theorem。
- `InitInner.lean:103-104`：docstring 稱 `pk1_len` 為「external axiom」，實為 `noncomputable opaque`（`FunsExternal.lean:1716`）。假設值 `64` 正確（libcrux `PublicKey1 = seed[32] + hash[32]`）。
- PR 描述稱此檔「在 Aeneas 更新時被刪、見 #649」：`git log origin/main` 顯示此檔從未在 main 上存在，#649 也不含此檔。描述不準確，但不影響內容。
- Issue #665 只要求 `Direction::from`；`init_inner` 為額外範圍。

### 公理相依（非本 PR 引入）
- `init_inner_spec_*` 依賴 `spqr.kdf.hkdf_to_slice_spec`（既有 axiom）與 `*._native.decide.ax_*`
  （來自 `SrcTranslated/Funs.lean` 中 `toStr "..."` 字串字面值）。main 上既有，非本 PR 問題。
