# FCA 双团驱动的证明重构总结（2026-08-04）

## 背景

`fca_bicliques.py` 在 定理 × 被引用引理 二部图上挖极大双团，
`fca-report-2026-08-02.txt` 榜首概念：

```
[area 32] 16 thms x 2 :: bind_tc_ok, hnext
```

extent = 16 个 `body_spec` 类定理（横跨 Poly/*、PolyEncoder/*、PolyDecoder/*、
EncodeVarint），intent = {`bind_tc_ok`, `hnext`}。

## 双团的真实含义

intent 两元素不是"被共用的定理"，而是同一段手写模板的碎片，被内联了 16 次：

```lean
obtain ⟨opt, iter1, hnext⟩ := <per-file 私有 helper> ...
rw [hnext]
simp only [bind_tc_ok]
```

- `bind_tc_ok`：单子左单位律 `(do let y ← .ok x; f y) = f x`，真定理。
- `hnext`：**局部假设名**（"迭代器 next 返回 ok"），各文件从不同私有
  helper（`EnumerateSliceIter_next_post`、`EnumerateSliceIter_next_Pt_some` 等）
  obtain 出来，恰好同名。

`hnext` 进入报告是词法提取的假阳性：FCA 脚本不走 probe-lean
（其依赖边从不指向 theorem），直接正则扫 `rw [...]` 括号内容；
假设名过滤器 `HYP_RE = ^(h|ih)([_A-Z0-9].*)?$` 要求 `h` 后跟
下划线/大写/数字，`hnext`（h + 小写 n）漏网。歪打正着——正是这个
漏网名字把"同一推理复制 16 份"的模式顶到榜首。

## 根因

- 时间线：这批证明写于 2026-06-10~17；上游 aeneas 的 `@[step]`
  enumerate spec（#1172）2026-06-30 才合入；仓库 pin 到 2026-07-24 后从未回填。
- 结构障碍：上游 `IteratorEnumerate.next_spec` 带高阶前提
  `h_inner : IteratorInst.next self.iter ⦃ ... ⦄`，`step` 对 match 形
  内层 spec 无法自动合一，直接用不上。

## 重构（两次提交）

### commit `fb34ba8` — enumerate 家族（net −146 行）

- 新文件 `Spqr/Specs/Aeneas/EnumerateSliceIterNext.lean`（+92）：
  泛型 `@[step] next_SliceIter_spec {T}`，组合特化到
  `Enumerate (Iter T)`，一阶前提，match 形后置条件
  （some 分支含取值、游标 +1、count +1 等式）。
- `RangeIteratorNext.lean`：给已有共享定理 `next_Usize_spec'` 补 `@[step]`。
- AddAssign −52（删 3 个私有 helper，去掉无调用者的 `h_self_len` 前提）、
  FromCompletePoints −92（删 5 个私有 helper）、ComputeAt −2。

### commit `8275310` — range 家族（net −47 行，13 文件）

17 处四行前奏统一替换为一行：

```lean
step as ⟨opt, iter1', h_none, h_some⟩
```

编译期连带修复：

1. LagrangeSum、PolyEncoder/FromPb 第 1 处：`step*`/`grind` 不会拆
   抽象 scrutinee 上的 match，需先 `obtain ⟨rfl, ...⟩ := h_some h_lt`
   具体化 `opt` 再 `step*`（ComputeAt 同款模式）。
2. LagrangeInterpolatePrepare、PolyDecoder/FromPb：`step as` 后
   `uncurry_apply_pair`、`index_slice_index` 变 unused simp arg
   （CI 视警告为失败），删除。

未动 2 处：PolyDecoder/IntoPb:176、PolyEncoder/IntoPb:284 走
`IteratorSliceIter.next_post`——现有 `@[step] next_spec` 的 some 分支
缺取值等式 `x = slice[i]`，替换会丢信息；覆盖它们需改 spec 陈述
（按仓库规约须人工过目）。

## 结果

- 合计 **net −193 行**，`lake build Spqr` 全绿，无新警告。
- 图论视角：K₁₆,₂ 双团（32 条显式引用边）塌缩为以共享 `@[step]`
  定理为中心的星形；下次 FCA 该概念应整体消失。
- 两层泛化缺一不可：数学层（泛型定理统一单态 helper）+
  自动化层（`@[step]` 注册让 `step as` 吞掉三步模板）。
  range 家族早有共享定理但没注册 `@[step]`，行数照样重复——
  第二层才是重复真正消失的原因。

## 待办 / 注意

- AI 撰写的 spec 陈述（`next_SliceIter_spec`、`h_self_len` 前提删除）
  按 CONTRIBUTING.md 须本人审阅后方可进 PR。
- 可选：给 `IteratorSliceIter.next_spec` 补取值等式，覆盖剩余 2 处
  `next_post` 调用点。
- 可选：修 `fca_bicliques.py` 的 `HYP_RE`（`h[a-z]` 也应算假设名），
  避免下次误报——但注意这类"假阳性"有时正是有用信号。
