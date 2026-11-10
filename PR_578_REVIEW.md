# PR #578 审核记录

- PR：[Add functional models for Chain ↔ protobuf conversion with round-trip proofs](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/578)
- 审核提交：`6975fba657bc1a44238ae06015032998d79f0231`
- 审核日期：2026-10-01
- 结论：发现 3 个需要修改的问题，建议暂缓合并。

## 1. [P1] 反序列化把非空队列的长度设为 0

位置：[Spqr/Specs/Chain/FunctionalModels.lean:122–125](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/blob/6975fba657bc1a44238ae06015032998d79f0231/Spqr/Specs/Chain/FunctionalModels.lean#L122-L125)

`fromPb` 收集完 epochs 后固定设置 `length := 0#usize`。但项目的 `VecDeque.from_iter` 将长度设置为实际收集的元素数，见 [SrcTranslated/FunsExternal.lean:3780–3792](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/blob/6975fba657bc1a44238ae06015032998d79f0231/SrcTranslated/FunsExternal.lean#L3780-L3792)。

即使 protobuf 输入包含一个合法 epoch，模型返回的队列长度仍为 0。这与实现语义不符，会使依赖该模型的推理把非空队列视为空队列，影响后续长度判断和密钥索引。相关 `fromPb ∘ intoPb` 及单子版本往返定理也重复了这个错误。

建议：将长度设置为 `epochs.length` 对应的 `Usize`，并同步修正往返定理的结论。`head` 可以归零，但 `length` 必须保留有效元素数。

## 2. [P1] 序列化包含已移出队列的元素

位置：[Spqr/Specs/Chain/FunctionalModels.lean:94–95](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/blob/6975fba657bc1a44238ae06015032998d79f0231/Spqr/Specs/Chain/FunctionalModels.lean#L94-L95)

`intoPb` 对整个 `self.links.buf.val` 做 `map`，忽略 `head` 和 `length`。项目的 `pop_front` 只更新这两个字段，不删除缓冲区内容，见 [SrcTranslated/FunsExternal.lean:1241–1256](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/blob/6975fba657bc1a44238ae06015032998d79f0231/SrcTranslated/FunsExternal.lean#L1241-L1256)。

例如缓冲区为 `[a, b]`，弹出 `a` 后，队列具有 `head = 1`、`length = 1`，有效元素只有 `[b]`，但此模型仍序列化 `[a, b]`。因此模型不能表示队列经过弹出操作后的正确序列化行为。

建议：按队列的有效元素及其逻辑顺序建模，而不是映射整个底层缓冲区；明确所需的队列表示不变量，并据此调整往返性质。

## 3. [P2] 解码规格未约束方向转换结果

位置：[Spqr/Specs/Chain/Chain/FromPb.lean:34–37](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/blob/6975fba657bc1a44238ae06015032998d79f0231/Spqr/Specs/Chain/Chain/FromPb.lean#L34-L37)

`from_pb_spec` 的后置条件只要求存在 `dirResult`，没有将它绑定到实际的 `try_from pb.direction` 及后续 `map_err` 的结果。

对任意输入和错误 `e`，选择 `dirResult := .Err e` 就会得到 `FunctionalModels.fromPb pb dirResult = .Err e`。因此，无论输入是否合法，返回任意错误都能满足这个后置条件；成功分支的方向也没有与 protobuf 的方向字段建立关联。该规格无法保证合法输入不会无故报错，或成功解码的方向正确。

建议：将 `dirResult` 与真实方向转换结果关联，类似 `into_pb_spec` 中对 `dirI32` 的约束，或在模型中直接表达方向解码规则。

## 验证范围

- 审核时，PR 的三个 CI 检查均通过。
- 在 `/tmp` 的隔离目录中，复用了本地现有依赖与构建产物，编译了两个 functional model 模块、方向转换模块、序列化闭包模块，以及新增的 `Chain/FromPb` 和 `Chain/IntoPb` 模块；同时确认两个新增文件可以共同导入。
- 未运行完整的干净构建。本地直接编译产生了许可证头配置警告和预期的 `sorry` 警告。
- 上述发现属于规格语义问题。编译通过不能排除这些问题，且连接 Chain 实现与模型的规格及单子往返定理仍使用 `sorry`。
- 本次审核未修改实现或证明文件，也未向 GitHub 发布评论。
