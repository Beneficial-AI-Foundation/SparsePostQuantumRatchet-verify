# Lean 内存优化流程

用 [`scripts/radar-memory.py`](../scripts/radar-memory.py) 测量单个 Lean 模块重新检查时的峰值 RSS 和耗时。先扫描全仓找热点，再对选定模块逐轮优化，最后复核全仓。脚本在本地运行，输出 Radar 兼容 JSONL 和原始日志；本地结果不会自动上传 Radar。

## 运行

在仓库根目录执行，环境需要 Linux、GNU time、Python 3、Git 和可用的 Lake 依赖。脚本默认覆盖 `Spqr`、`SrcTranslated`、`HeaderLinter`、`Utils`、`Tests` 中的项目模块；不包含 `.lake/packages` 或独立审计脚本。它逐模块构建依赖、预热一次，再用 `lake env lean -j1 --setup <模块的 Lake setup.json>` 测量，确保使用 Lake 的模块选项和 linter 配置。全程使用同一机器、工具链、脚本和测量条件，避免同时运行其他大内存任务。

```bash
set -euo pipefail
session="$(mktemp -d /tmp/spqr-memory.XXXXXX)"

# 全仓初筛：每模块一次，只用于排名。
python3 scripts/radar-memory.py "$PWD" --list-modules > "$session/all-modules.txt"
python3 scripts/radar-memory.py "$PWD" "$session/scan-before.jsonl" \
  --modules-file "$session/all-modules.txt" --trials 1
python3 - "$session/scan-before.jsonl" <<'PY'
import json, sys
rows = [json.loads(line) for line in open(sys.argv[1])]
for row in sorted((r for r in rows if r["metric"].endswith("//peak-rss-median")),
                  key=lambda r: r["value"], reverse=True):
    print(f'{row["value"] / 1024**2:.1f} MiB  {row["metric"]}')
PY

# 从排名中选热点，并加入本轮修改的依赖及受影响下游；每行一个模块名。
# 编辑 "$session/round-modules.txt" 后建立三次基线。
python3 scripts/radar-memory.py "$PWD" "$session/baseline.jsonl" \
  --modules-file "$session/round-modules.txt"

# 每轮修改并通过正确性检查后，使用新的输出路径复测。
python3 scripts/radar-memory.py "$PWD" "$session/round-01.jsonl" \
  --modules-file "$session/round-modules.txt"

# 结束时重新发现模块并全仓复核。
python3 scripts/radar-memory.py "$PWD" --list-modules > "$session/all-modules-final.txt"
python3 scripts/radar-memory.py "$PWD" "$session/scan-after.jsonl" \
  --modules-file "$session/all-modules-final.txt" --trials 1
```

JSONL 每模块包含 `peak-rss-median`、`peak-rss-max`（字节）和 `elapsed-median`（秒）。`--trials 1` 使用 `memory-scan-j1/` 前缀，三次测量使用 `memory-j1/`；不要跨两种结果计算改善率。检查 `NAME.logs/modules.txt` 与指标数量是否一致，失败运行不能作为基线。已有完整扫描仅在源码、模块清单和测量条件一致时复用；初筛仍不能代替热点的三次基线。旧版脚本仅传入 `maxRecDepth`，没有加载 Lake setup；它的结果不能与当前脚本结果直接比较。

## 每轮决定

1. 从全仓 RSS 排名选择可修改的热点，固定本轮模块清单。一次只处理一个原因，例如收窄 `simp`／`grind` 搜索、抽取共享证明、给大型不变量命名或减少公开导入。不手改生成的 `Types.lean`／`FunsCore.lean`／`Funs.lean`。
2. 保持定理含义和信任依赖，不新增 `sorry` 或公理。构建受影响模块及下游；保留候选前运行 `lake build`、`lake exe runLinter Spqr`、`lake env lean scripts/Audit.lean` 和 `git diff --check`。
3. 比较同一模块在 `baseline.jsonl` 与本轮 JSONL 中的三项指标。默认保留门槛：目标 RSS 中位数下降至少 5%，耗时中位数增加不超过 10%，下游无明显回退。收益接近测量波动时，交替重测基线和候选。保留后以候选作为下一轮基线；否则只撤回本轮修改。
4. 最后比较两次全仓扫描的覆盖、热点和回退；对疑似回退模块分别补做三次测量。模块增删单独记录，不能把少测模块当作改善。修改公共导入、生成方式或工具链时，每轮都做全仓复核。

每轮记录源码状态、模块清单、JSONL 和 `.logs/` 路径、RSS／耗时变化、正确性检查及保留理由。日志保存脚本、环境、源文件快照和已跟踪改动；未跟踪的其他依赖源码需另行留存。`/tmp` 中的结果应在清理前归档。

此指标是单个 Lean 进程的峰值，包含启动和导入，不代表整个并行构建的总内存，也不测 Rust 运行时堆内存。需要历史、团队共享或提交对比时，再按 [PERFORMANCE.md](PERFORMANCE.md) 使用远程 Radar；先确认远程 run 实际包含逐模块 RSS，不能把指令数或 `build//maxrss` 当作本脚本的指标。
