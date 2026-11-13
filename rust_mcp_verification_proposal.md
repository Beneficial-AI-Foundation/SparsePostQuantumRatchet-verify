# Rust MCP SDK 形式化验证提案

## 1. 对象与动机

本提案所说的“Rust MCP 实现”是 [Model Context Protocol 官方 Rust SDK](https://github.com/modelcontextprotocol/rust-sdk)，核心 crate 为 `rmcp`，另有生成工具实现的 `rmcp-macros`。SDK 同时提供 MCP 客户端和服务端能力，覆盖消息模型、请求分发、工具等功能，以及 stdio 和 Streamable HTTP 传输。MCP 让 AI 客户端发现并调用外部工具、读取资源；因此，协议状态错误、请求与响应错配或权限边界错误，都可能影响实际的工具调用。[官方 SDK 说明](https://github.com/modelcontextprotocol/rust-sdk/blob/main/README.md) | [MCP 工具规范](https://modelcontextprotocol.io/specification/2025-11-25/server/tools)

验证的价值是为关键协议行为提供可检查的、针对具体源码版本的保证。已有的 [SDK 安全公告](https://github.com/modelcontextprotocol/rust-sdk/security/advisories) 也表明 HTTP 会话管理、重定向和授权元数据等边界值得关注。但本提案不预设这些历史问题仍存在于拟验证版本中；选定提交后需重新核对修复状态。

## 2. 与当前项目的关系

本仓库验证的是 Signal 的 [Sparse Post-Quantum Ratchet Rust 实现](README.md)，使用 Aeneas 将 Rust 代码翻译成 Lean，再证明函数规格及更高层性质。MCP SDK 是另一个代码库和协议，与 SPQR 没有已知的直接调用或密码协议依赖关系。两者的关联是验证方法：可以复用本仓库在版本固定、Rust 提取、Lean 规格、翻译边界审计和持续构建方面的经验，而不能直接复用 SPQR 的安全定理来证明 MCP。

建议在独立仓库或独立实验分支启动，以免把两个不同的信任边界混在一起。第一阶段只研究 `rmcp` 中可独立提取的协议核心；HTTP、OAuth、Tokio 调度和外部网络栈待可行性评估后再决定是否纳入。

## 3. 验证目标与范围

**第一阶段目标：**固定 `rust-sdk` 的提交和协议版本，建立一个通过 Lean 检查的 MCP 请求处理模型，并将至少一个真实 Rust 函数与其规格连接起来。建议从 `2025-11-25` 的初始化与工具调用子集开始；该版本的生命周期要求初始化、版本与能力协商，再进入正常操作。[生命周期规范](https://modelcontextprotocol.io/specification/2025-11-25/basic/lifecycle)

候选性质按优先级排列：

| 优先级 | 性质 | 可检查的断言 |
| --- | --- | --- |
| P0 | 生命周期与能力协商 | 初始化前不能处理普通工具请求；协商后的版本和能力约束后续分发。 |
| P0 | 请求与响应关联 | 每个成功处理的请求得到匹配的响应 ID；通知不被错误地当成请求响应。 |
| P1 | 工具调用分发 | `tools/call` 只能分发到已注册的工具；未知名称或参数错误进入明确的错误路径。 |
| P1 | 传输边界 | stdio 的逐行消息解析不会把非协议输出当成协议消息；HTTP 的 Origin、会话与认证边界另立规格。 |

这些是**待证明的目标**，不是对当前 SDK 的已验证结论。`2026-07-28` 版引入与旧版不同的无状态生命周期，因此若选择该版本，需要另写对应规格，不能沿用“初始化前”性质。[SDK 版本说明](https://github.com/modelcontextprotocol/rust-sdk/blob/main/README.md)

## 4. 技术路线与交付物

1. **固定基线（约 1 周）：**记录 SDK commit、`Cargo.lock`、启用的 Cargo features、目标 MCP 规范版本和最小调用路径；列出涉及的源码函数、依赖与已知安全公告。交付范围清单与信任边界图。
2. **提取试验（约 1–2 周）：**选择消息类型、版本协商或工具名查找中的一个纯逻辑函数，用 Aeneas/Charon 尝试翻译。记录无法翻译的 `async`、宏、trait、第三方库部分及所需抽象；保留 Rust 原函数与翻译产物的对应记录。交付可重现的提取脚本和障碍清单。
3. **规格与首个证明（约 2–4 周）：**在 Lean 中定义请求、响应、协议状态与转移关系，证明至少一个具体性质，并尽可能把证明绑定到提取后的 Rust 函数。交付可构建的 Lean 文件、定理陈述和信任假设列表。
4. **扩展决策（约 1 周）：**根据提取覆盖率和证明成本，决定继续验证协议核心、stdio 边界，或为 HTTP/OAuth 另建项目。交付下一阶段范围、工时估算和未覆盖风险。

每个里程碑应附 `cargo test`、提取命令与 `lake build` 的可重现结果。测试用于发现实现问题；形式化结论仅以已证明的定理、所用假设及对应源码版本为准。

## 5. 难度与主要风险

总体难度为**高**。本仓库的 Aeneas 流程已经处理过部分 Rust 代码，但 MCP SDK 大量使用异步执行、宏生成、trait、网络 I/O 和第三方库；这些部分未必能直接提取。仅有抽象状态机的证明不能自动代表 `rmcp` 源码正确。HTTP 和 OAuth 的端到端安全还涉及运行时、代理、配置及外部身份提供方，其证明范围会显著大于协议核心。[MCP 传输规范](https://modelcontextprotocol.io/specification/2025-11-25/basic/transports) | [安全实践](https://modelcontextprotocol.io/docs/2025-11-25/tutorials/security/security_best_practices)

上述 **5–8 周** 是单人探索性工作量估计，前提是选定的小函数可以提取；不是完整 SDK 验证工期。若第 2 步无法把任何目标函数与 Rust 源码连接，应先缩小到独立的、无 I/O 的协议算法，并明确把结果标为“模型验证”。若连接成功，再以覆盖率和每条性质的证明成本估算后续工作。

## 6. 第一阶段完成标准

- 提案对应一个固定的 SDK commit、Cargo features 与 MCP 规范版本。
- 至少一个性质有 Lean 定理和成功的 `lake build` 记录。
- 明确标出该定理对应的 Rust 函数或仅对应抽象模型；所有 opaque/外部假设均可审阅。
- 给出未覆盖的 HTTP、OAuth、异步运行时与宏生成代码清单，以及是否进入下一阶段的依据。
