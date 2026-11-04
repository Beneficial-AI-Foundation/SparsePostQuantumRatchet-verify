# 逐轮降低 Lean 内存消耗

本流程默认优化本仓库的 Lean 编译／证明检查峰值内存。
**先建立全仓逐模块内存／耗时排名，再选择热点逐轮优化，最后全仓复核。**
Radar 负责运行 benchmark、保存指标、展示历史和比较提交；具体覆盖范围和指标由 benchmark
脚本决定。不能把“Radar 支持全仓测量”误解为“现有配置已采集全仓逐模块 RSS”。
优先复用同条件、覆盖完整的远程 Radar 结果；缺少逐模块内存指标时先配置后文的 `memory` run。
本地工作区使用同一份 Radar 兼容脚本，可在无需提交的情况下完成每轮实验；结果以 JSONL 和
原始日志保存。必须明确标注“本地 Radar 兼容测量”或“远程 Radar run + URL”，不能混称。
Rust 协议运行时的堆内存是另一项指标，需要固定输入的 Rust benchmark，不能用 Lean 数据代替。

## 循环

**全仓扫描 → 热点基线 → 修改一个原因 → 正确性检查 → 每轮复测 → 保留或撤回 → 全仓复核。**

1. **全仓扫描。** 记录提交、已有未提交改动、Lean 版本、锁文件、机器、线程数、脚本版本
   和模块清单。按下文覆盖所有项目库模块，串行采集每个文件的峰值 RSS 和耗时，分别排序。
   初筛可预热后测一次，但不能据此宣布优化达标；历史热点只用于辅助解释，不能替代全仓排名。
   检查预期模块数与实际成功数，明确排除项。OOM、超时或失败必须记录并优先排查，不能跳过
   后把剩余模块称为完整排名；失败运行不是有效基线。
2. **热点基线和定位。** 从全仓排名选出高 RSS 模块，并加入本轮修改的依赖模块及受影响下游，
   固定本轮清单，预热后各测三次。已有远程数据只有在源码、模块覆盖、脚本、runner、线程和
   测量方式可比时才可复用。可用 `lake env lean --profile 文件.lean` 辅助找耗时声明；
   Radar 的文件级 RSS 不会自动定位到定理内部。可另测仅含导入的文件来估计加载成本，
   但不能将两次峰值简单相减当作证明的精确内存。
3. **提出一个假设。** 例如大型自动化搜索产生过多中间项、重复展开大定义，或导入过多模块。
   每轮从下方历史 PR 技巧中选择一个原因，写明预期影响的模块。
   一个原因可以涉及多个必要改动，但不要同时混入导入调整、证明重写和工具链升级。
4. **做最小修改。** 优先复用已有引理、用明确引理列表替换宽泛搜索、拆出可复用辅助引理、
   减少不必要展开或导入。遵循仓库风格规范，不手改自动生成的 `Types.lean`／`Funs.lean`。
5. **检查正确性。** 不改变定理含义，不新增 `sorry`／公理、不关闭检查来换取内存下降。
   构建受影响模块及下游；准备保留时运行下方完整检查。
6. **每轮用 Radar 指标复测并决定。** 每轮修改并通过正确性检查后，运行同一内存 benchmark；
   可在本地检查当前工作区，或在已接入的远程 Radar 上比较提交。不能只看指令数或 build 总 RSS。
   固定脚本、模块清单和线程数，预热后测三次，与当前已接受基线比较；保留最大值和耗时。
   默认接受门槛：目标模块 RSS 中位数下降至少 5%，且耗时中位数增加不超过 10%；
   受影响下游出现超过波动范围的回退时先排查，不能只报告最佳模块。
   这是工作阈值；若重复测量波动已接近收益，增加交替的基线／候选测量，暂不宣布改善。
   无收益或不正确时，只撤回本轮自己的修改，保留用户已有改动。
7. **进入下一轮。** 达到性能门槛且通过完整检查的候选成为新基线；保存其 JSONL 和源码快照。
   撤回候选时继续使用上一个已接受基线；记录成功和失败实验。
   新一轮若改变模块清单，先在已接受源码上补齐新清单的三次基线，不能沿用缺少模块的数据。
   达到预定内存目标、连续三轮没有可复现收益，或达到约定轮数时停止并汇报。
8. **全仓复核。** 保留候选前完成完整正确性检查；结束时对最终源码重跑全仓扫描，对照初始
   全仓结果检查最大热点、各模块回退和排名变化。修改公共导入、生成代码的生成方式或工具链等
   广泛依赖时，每轮都做全仓复核。发现疑似回退后对相关模块的基线／候选各测三次再决定。
   新增／删除／重命名模块单独列出，比较共同模块；不能把少测了文件当作内存改善。
   单次全仓初筛只能用于发现问题，正式收益仍须来自同条件三次复测。

## 执行入口：全仓扫描与逐轮复测

环境要求：Linux、GNU time（`/usr/bin/time`）、Python 3、Git 和可用的 Elan/Lake 依赖环境。
脚本 [`scripts/radar-memory.py`](../scripts/radar-memory.py) 默认覆盖 `lakefile.toml` 中
`Spqr`、`SrcTranslated`、`HeaderLinter`、`Utils`、`Tests` 五个库的根文件及目录下所有
`.lean` 文件，包括生成模块、测试模块和 `Utils.Status` 可执行入口。包含工作区未跟踪源码。
不包含 `.lake/packages` 的第三方库、`scripts/Audit.lean` 等独立检查脚本；后者单独执行。
这一定义称为“全仓项目模块”，不等于所有依赖源码。Lake 新增库或调整源目录时，须同步
更新脚本 `ROOTS`／发现规则并审阅清单，避免遗漏。测试库不属于默认 `lake build`，本脚本
仍逐模块构建它们；如环境缺失导致失败，修复后重跑，不能静默排除。

每个模块先构建自身及依赖（不计入指标），预热一次，再独立执行 `lake env lean -j1`。
默认测三次；`--trials 1` 用于全仓初筛，使用独立 `memory-scan-j1/` 指标前缀；三次复测使用
`memory-j1/`。两种结果不能直接作为同一性能序列比较。依赖构建、预热或任一次测量失败均
非零退出，不生成可接受的 JSONL；保留失败日志，修复后使用新的输出路径重跑。

### 1. 固定全仓清单并初筛

在仓库根目录、同一终端执行；默认全仓三次可能较慢，下面先每模块测一次：

```bash
set -euo pipefail
session="$(mktemp -d /tmp/spqr-memory-local.XXXXXX)"
python3 scripts/radar-memory.py "$PWD" --list-modules > "$session/all-modules.txt"
wc -l "$session/all-modules.txt"
python3 scripts/radar-memory.py "$PWD" "$session/scan-before.jsonl" \
  --modules-file "$session/all-modules.txt" --trials 1
python3 - "$session/scan-before.jsonl" "$session/all-modules.txt" <<'PYRANK'
import json
from pathlib import Path
import sys
rows = [json.loads(line) for line in Path(sys.argv[1]).read_text().splitlines()]
expected = set(Path(sys.argv[2]).read_text().splitlines())
assert len(rows) == len({r["metric"] for r in rows}) == 3 * len(expected)
for suffix, scale, unit in [("peak-rss-median", 1024**2, "MiB"), ("elapsed-median", 1, "s")]:
    values = [r for r in rows if r["metric"].endswith("//" + suffix)]
    assert {r["metric"].split("/module/")[1].split("//")[0] for r in values} == expected
    print(f"\nRanking: {suffix} ({len(values)}/{len(expected)} modules)")
    for row in sorted(values, key=lambda r: r["value"], reverse=True):
        print(f'{row["value"] / scale:.2f} {unit}  {row["metric"]}')
PYRANK
```

已有远程全仓 `memory` run 的三次结果也可用于排名，但必须核对完整覆盖，且不能与本地
单次初筛直接计算改善率。不要预先固定 Gc、FromCompletePoints、PolyReduce 为唯一热点。

### 2. 根据排名建立本轮三次基线

将选中的热点、修改的依赖模块以及受影响下游写入 `$session/round-modules.txt`，每行一个
完整模块名，无注释、不重复。根据导入关系确定下游；公共基础依赖影响面大时使用全仓清单。
选择依据、排除理由和模块数量必须记入每轮记录。创建清单后执行：

```bash
baseline="$session/baseline.jsonl"
python3 scripts/radar-memory.py "$PWD" "$baseline" \
  --modules-file "$session/round-modules.txt"
```

### 3. 每轮复测并比较

每轮修改、完成正确性检查后执行（每轮使用新文件名，不覆盖旧结果）：

```bash
round=01                       # 下一轮改为 02、03……
candidate="$session/round-$round.jsonl"
python3 scripts/radar-memory.py "$PWD" "$candidate" \
  --modules-file "$session/round-modules.txt"
python3 - "$baseline" "$candidate" <<'PYCOMPARE'
import json
from pathlib import Path
import sys

def read(path):
    rows = [json.loads(line) for line in Path(path).read_text().splitlines()]
    assert rows and len({r["metric"] for r in rows}) == len(rows)
    return {r["metric"]: r for r in rows}

base, candidate = map(read, sys.argv[1:])
assert base.keys() == candidate.keys(), "module/metric lists differ; remeasure baseline"
for metric in sorted(base):
    assert base[metric]["unit"] == candidate[metric]["unit"]
    before, after = base[metric]["value"], candidate[metric]["value"]
    delta = (after / before - 1) * 100
    unit = base[metric]["unit"]
    scale = 1024**2 if unit == "B" else 1
    print(f'{metric}: {before/scale:.2f} -> {after/scale:.2f} '
          f'{"MiB" if unit == "B" else unit} ({delta:+.2f}%)')
PYCOMPARE
```

RSS 变化为负表示下降；对本轮目标模块检查中位数至少下降 5%、耗时增长不超过 10%，
并检查受影响下游及最大值。比较脚本只展示结果，不自动保留或撤回修改。
保留并通过完整检查后执行 `baseline="$candidate"`；否则只撤回本轮改动，保持 `baseline`。
失败的运行保留日志，修复后换一个新输出文件名重跑，不把失败计入性能基线。

每份 `NAME.jsonl` 旁有 `NAME.logs/`，包含每次 RSS/耗时、Lean 输出、环境、锁文件、
脚本副本、模块清单、测量配置、被测源文件副本及相对 HEAD 的已跟踪改动补丁。
未跟踪的其他依赖源码须另行归档；HEAD 哈希不能替代工作区快照。
不要在测量期间修改源码、切换分支或并发运行其他 benchmark。
每轮记录两个结果路径和对应源码状态，结束后将 `/tmp` 会话目录复制到持久存储。

### 4. 最终全仓复核

模块集合未变化时复用全仓清单；有变化时先重新发现并记录增删，再分析共同模块：

```bash
python3 scripts/radar-memory.py "$PWD" --list-modules > "$session/all-modules-final.txt"
diff -u "$session/all-modules.txt" "$session/all-modules-final.txt" || true
python3 scripts/radar-memory.py "$PWD" "$session/scan-after.jsonl" \
  --modules-file "$session/all-modules-final.txt" --trials 1
```

用上面的排名代码核对覆盖，用比较代码对照 `scan-before.jsonl` 和 `scan-after.jsonl`
（清单变化时先分离共同模块）。对疑似回退补做三次基线／候选测量，并记录最终判断。
扫描无回退不替代前面的完整正确性检查，也不把各文件 RSS 求和称为构建峰值。

上述命令是本地 Radar 兼容 benchmark，不会上传结果或启动 Radar 服务。
需要远程历史、团队共享和提交对比时，按下文接入；未接入时明确记录缺失项。

## 从历史 PR 提取的优化技巧

2026-10-28 检索本仓库 PR 描述、代码 diff 和 Radar 评论。
主要作者是 Oliver Butterley（`oliver-butterley`）和 Hoang Le Truong（`truonghoangle`）。
下面是可复用的实验方向，不是已经证实的 RSS 降幅：大部分历史报告给出的是
`//instructions` 和 `//wall-clock`，指令数下降不意味着峰值内存同比下降。
对内存机制的解释属于根据改动提出的假设，必须用本流程复测。

### 1. 明确执行步骤，减少自动搜索

Oliver 的 [#671](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/671/files)
和 [#674](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/674/files)
把多处 `step*` 改为 `step as ⟨…, h…⟩`、`step with 某个_spec`，
用 `WP.spec_mono (body_spec …)` 明确应用循环体规格，再分别处理继续／终止分支。
后置条件直接通过命名的假设、`exact`、`rw` 和局部算术证明构造。

**一轮实验：** 只改一个热点循环的自动步骤，保留规格和循环不变量。
假设是减少搜索及分支处理中产生的中间状态。不要机械替换全部 `step*`。

### 2. 用局部推理替换大范围 `grind`／`simp_all`

Oliver 的 [#675](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/675/files)
在 `Poly.AddAssign` 中把系数更新的 `grind` 改为按索引分类、明确 `rw` 和 `exact`；
长度算术先写成 `.val.length` 等一致形式，再交给 `omega`。
[#670](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/670/files)
删除了反复执行 `simp only [alloc.vec.Vec.length] at *; omega` 的 `vecOmega` 宏，
将需要的长度事实预先命名并直接传递。

**一轮实验：** 只替换一个高成本求解点，或只消除一组重复的全上下文简化。
优先利用已有等式，避免每个小目标都重新扫描大型上下文。

### 3. 共享重复证明，分支只负责传参

Oliver 的 [#668](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/668/files)
让平台版本复用 `key_spec_all_core`，例如 `key_spec_32` 仅准备边界条件并调用公共证明。
[#672](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/672/files)
在 `FromCompletePoints` 中提取 `arm_spec`，让 1、3、5、30、34、36 六种常量分支复用。

**一轮实验：** 只提取一组相同分支的公共引理，避免重复展开、搜索和 elaboration。
历史 #668 还删除了冗余前提，属于加强规格；本流程默认保持公开规格不变，
若要加强规格，应另行说明，避免和性能改动混在一起。

### 4. 给大型循环不变量命名

Oliver 的 [#670](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/670/files)
用 `private structure GcLoopInv … : Prop` 表达原先很长的合取式不变量，
循环里引用 `GcLoopInv …`，需要时才拆开其字段。

**一轮实验：** 仅改变一个不变量的组织方式，保持所有字段含义不变。
这是减少大表达式反复处理的候选方法；该 PR 同时包含其他重写，不能把整个 PR 的收益
单独归因于 `structure`，也不能保证命名后 RSS 必然下降。

### 5. 收窄模块的公开依赖

Truong 的 [#651](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651)
迁移到 Lean `module` 系统，明确公开导入和声明可见性；Oliver 也参与了修改。
Oliver 随后的 [#660](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/660/files)
将只用于本文件证明的部分 `public import` 改为 `import`，并为下游补充实际需要的依赖。

**一轮实验：** 选择一个模块，检查哪些导入只用于证明、哪些必须对外提供。
测量该模块及代表性下游；不要仅看当前文件。仓库已经迁移，无需重做 #651。
本次检索没有找到足以引用为 Truong 独立 RSS 优化成果的前后测量，故这里只列可核实的改动。

### 6. 大型计算证明：优先研究符号证明

Oliver 的 [#718](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/718)
将八个 NTT 相关 `decide +kernel` 改为 `native_decide`，作为恢复 Radar 构建的临时方案。
后续 [#721](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/721)
明确记录原计算证明的内存问题，并提出补充符号证明或决定是否接受原生计算的信任要求。

**一轮实验：** 选一个计算规模大的等式，用数学恒等式和辅助引理代替穷举归约。
本流程不自动把 `decide +kernel` 替换成 `native_decide`：后者改变信任依赖，
需要单独评估，不能当作保持原有信任边界的普通性能修改。

### 历史数据怎样用

| PR | Radar 评论中的指标例子 | 对本流程的意义 |
|---|---|---|
| [#668](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/668#issuecomment-6213415201) | Key32 指令数 −92.13% | 优先研究公共核心证明；不是 RSS −92.13% |
| [#672](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/672#issuecomment-6235525878) | FromCompletePoints 指令数 −69.74% | 优先研究重复分支；需本地测内存 |
| [#670](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/670#issuecomment-6235586922) | Gc 指令数 −41.11%，blocked 时间上升 | 减少指令与减少耗时、内存应分别评估 |
| [#660](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/660#issuecomment-6163386404) | bench repo 版本不同的警告 | 不从该对比推导确定的性能收益 |
| [#718](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/718#issuecomment-6341121076) | 作者指出基线构建失败 | 只能证明恢复构建，不能用不完整基线计算完整构建收益 |

历史 PR 往往一次用了多种技巧。新实验应拆开验证，例如先只限制自动搜索，
下一轮再共享重复引理，再下一轮才调整公开导入。推荐在每轮记录中增加：
`参考 PR / 本轮唯一假设 / 修改范围 / RSS 实测 / 是否保持规格与信任依赖`。

## 手工测量命令（排查或自定义模块时使用）

以下在仓库根目录用 Bash 执行。示例模块只是演示，请换成实际热点。
每轮设置唯一的 `label`；修改公共依赖后，必须重新构建，使导入的产物保持最新。

```bash
set -euo pipefail
module=Spqr.Math.List
file=Spqr/Math/List.lean
label=baseline                 # 后续用 round-01、round-02 等
out="$(mktemp -d /tmp/spqr-memory-${label}.XXXXXX)"

git rev-parse HEAD > "$out/commit.txt"
git status --short > "$out/status.txt"
git diff --binary > "$out/working-tree.patch"  # 未跟踪源码需要另行留存
lake env lean --version > "$out/lean-version.txt"
cp lean-toolchain lake-manifest.json "$out/"
uname -a > "$out/machine.txt"

# 准备依赖，失败则停止。此步骤不计入单文件测量。
lake build "$module" > "$out/build.log" 2>&1

# 统一为热缓存；独立启动 Lean，每次重新检查源文件，不测 Lake 的缓存命中。
lake env lean -j1 "$file" > "$out/warmup.log" 2>&1
for run in 1 2 3; do
  /usr/bin/time -f 'max_rss_kib=%M\nelapsed_s=%e\nexit=%x' \
    -o "$out/run-${run}.metrics" \
    lake env lean -j1 "$file" > "$out/run-${run}.log" 2>&1
done
printf '结果目录：%s\n' "$out"
cat "$out"/*.metrics
```

Linux GNU time 的 `%M` 是最大驻留内存，单位 KiB，除以 1024 得到 MiB。
这里测的是单文件 Lean 检查（含启动和导入），并非完整构建的同时总内存。
`-j1` 固定了本实验的 Lean 线程数，不能把降低并发本身算作证明优化收益。
避免同时运行其他编译或大内存任务；所有轮次使用同样的缓存和线程策略。

不要把 `/usr/bin/time lake build` 的 `%M` 当成所有并行子进程的同时总 RSS。
若目标是整仓构建 OOM，需要另测隔离 cgroup 的 `memory.peak`，固定构建并发、
相同构建产物初始状态，并单独报告该指标（它还可能包含页缓存等内存）。
也不要把多次增量构建的缓存命中当成完整构建内存改善。

候选保留前，按当前 CI 方式检查：

```bash
lake build
lake exe runLinter Spqr
lake env lean scripts/Audit.lean
git diff --check
```

检查日志中的新警告，并比较基线与候选的审计结果；命令成功不替代对新增假设的检查。
若涉及测试库或提取流程，再执行相应检查。

## 远程 Radar：全仓覆盖、历史和提交对比

Radar 的 server 保存结果并提供网页，runner 在被测提交上执行 bench repo 中的脚本。
内存仍由脚本采集；**只打开 Radar 页面、或在本地用 GNU time 测量，不等于已运行 Radar**。
开始优化前先核对远程指标和覆盖；有可比全仓结果时直接利用。若缺少配置，可先用本地
全仓入口完成诊断，但不能宣称已在远程 Radar 检测了所有文件。配置和提交发布须遵循当前
会话授权；本流程不要求为每次尚未验证的本地尝试提交、推送或发送评论。

### 1. 先查看现有远程结果

1. 打开[本仓库 Radar 页面](https://radar.18.118.100.156.nip.io/repos/SparsePostQuantumRatchet-verify)，
   选择目标提交，确认 run 成功，并记录被测提交、bench repo 提交和 runner。
2. 先查逐模块 `memory-j1/module/<模块名>//peak-rss-median` 和 `elapsed-median`，
   核对模块清单及覆盖数量。只有 `build//maxrss` 时，只有 build 级内存指标，需接入下一节。
   `build/module/<模块名>//instructions` 是指令数，不能用于内存排名；lakeprof 的耗时表也不能。
3. 在 PR 中评论 `!radar` 可以请求已配置的 benchmark；结果由机器人回复。
   要比较优化效果，基线和候选都必须成功，且使用同一 bench 版本、runner 和测量条件。
   `!radar` 不会自动添加尚未配置的内存指标。

2026-10-28 核对的 bench repo 版本是
[`249d6c120ba3f62bb86ad86435a65cfe49a5d933`](https://github.com/Beneficial-AI-Foundation/lean-bench-scripts/tree/249d6c120ba3f62bb86ad86435a65cfe49a5d933)。
其 [`build/run`](https://github.com/Beneficial-AI-Foundation/lean-bench-scripts/blob/249d6c120ba3f62bb86ad86435a65cfe49a5d933/scripts/bench/build/run)
请求整次构建的 `maxrss`，但
[`lean.py`](https://github.com/Beneficial-AI-Foundation/lean-bench-scripts/blob/249d6c120ba3f62bb86ad86435a65cfe49a5d933/scripts/bench/build/fake-root/bin/lean.py)
只请求每模块的 `instructions`，没有每模块 RSS。
此外，该版本的
[`measure.py`](https://github.com/Beneficial-AI-Foundation/lean-bench-scripts/blob/249d6c120ba3f62bb86ad86435a65cfe49a5d933/scripts/bench/measure.py)
把 Linux `ru_maxrss` 乘以 **1000** 后标成 `B`，而 KiB 应乘以 **1024**。
因此旧 `build//maxrss` 的绝对字节值不能直接与下方新指标比较。
它也不是各并行子进程同时总 RSS；整仓 OOM 分析仍需单独采集 cgroup `memory.peak`。

### 2. 在 bench repo 添加全仓内存脚本

推荐给本仓库增加独立的 `memory` run，保留现有 build benchmark。
将本仓库的 `scripts/radar-memory.py` 复制到 **bench repo** 的 `scripts/bench/memory/run`，并执行
`chmod +x scripts/bench/memory/run`。runner 需要 Linux、GNU time、Python 3、Git、
Elan/Lake 及构建依赖所需的网络或缓存。不需要 `perf` 权限。

两参数入口默认自动发现所有项目库模块，固定 `-j1`、一次预热和三次测量，因此远程
`memory` run 覆盖全仓项目模块。归档发现的 `modules.txt` 并核对覆盖；脚本版本改变时重新
测基线。多个模块串行测量，不能并行运行本脚本实例。若 runner 的时间／内存限制无法完成，
先记录失败并调整资源或设计有明确覆盖校验的分片，不能无声退回三个模块。

脚本已保存在本仓库的 [`scripts/radar-memory.py`](../scripts/radar-memory.py)，
本地循环直接调用它。远程接入时，将同一文件复制到 bench repo 的
`scripts/bench/memory/run` 并设置可执行权限，避免维护两份不同的测量逻辑。

任何依赖构建、预热或测量失败都会非零退出，不输出部分性能结果；原始日志保留在
输出文件旁的 `.logs/` 目录，需自行归档。Radar 自动保存脚本 stdout/stderr 和退出码，并不会自动上传
这个目录里的文件。该脚本测的是重新检查源文件的进程峰值，包含启动和导入，不是 Lake
缓存命中，也不是整个构建的总峰值。

每个模块只输出一条中位数、一条最大值和一条耗时中位数。
**Radar 会累加同名指标**，不能把三次 RSS 直接用同一 metric 输出，也不要同时把同一条
measurement 写进 JSONL 和 `radar::measurement=` 日志。这里用独立的 `memory-j1/` 前缀，
避免与旧的 `build//maxrss` 混淆。

### 3. 本地预检同一脚本

在 bench repo 根目录执行（替换被测仓库绝对路径）：

```bash
set -euo pipefail
repo=/absolute/path/to/SparsePostQuantumRatchet-verify
out="$(mktemp -d /tmp/spqr-radar-preview.XXXXXX)"
./scripts/bench/memory/run "$repo" "$out/measurements.jsonl" > "$out/run.log" 2>&1
python3 - "$out/measurements.jsonl" <<'PY'
import json
import sys
from pathlib import Path
rows = [json.loads(line) for line in Path(sys.argv[1]).read_text().splitlines()]
assert rows and len({r["metric"] for r in rows}) == len(rows)
for row in sorted(rows, key=lambda r: r["value"], reverse=True):
    if row["metric"].endswith("//peak-rss-median"):
        print(f'{row["value"] / 1024**2:.1f} MiB  {row["metric"]}')
PY
```

这一步验证脚本与 JSONL，并打印已测模块的内存排名；**不会上传 Radar**。
本地预检会读取工作区当前内容，正式 runner 则克隆已提交版本，不能把两者误认为同一次 run。
两参数入口已默认全仓；仍须核对日志中的 `modules.txt` 与实际指标数量，不能仅凭 run 成功推断覆盖。

### 4. 接入现有 server／runner，再做提交对比

由 Radar 维护者将脚本提交到 bench repo，更新 server 中本仓库对应的 bench 配置。
在现有 `benchRuns` 中追加以下条目，保留其他 run；runner 名必须是已配置的专用 runner：

```yaml
benchRuns:
  # 保留现有条目，再追加：
  - name: memory
    script: scripts/bench/memory/run
    runner: YOUR_EXISTING_RUNNER_NAME
```

`benchUrl` 指向包含脚本的 bench repo，`benchRef` 指向相应引用。
配置字段可对照 Radar 的
[`config-server.yaml`](https://github.com/leanprover/radar/blob/master/radar/config-server.yaml)。
自建服务时同样需要配置 server 和 runner；先固定 Radar 版本，使用该版本的配置与部署脚本。
本节不假定用户已有远程配置权限，也不通过修改本仓库文件冒充已完成远程接入。

接入后按以下顺序操作：

1. 提交候选源码，让 runner 能克隆到；在 PR 评论 `!radar` 请求测试。
   确认新增的 `memory` run 被执行且覆盖完整清单，不能只看到旧 `main` run 成功就认为测过逐模块内存。
2. 确认基线提交也有同一 bench 版本的成功 `memory` run。若缺失，请维护者重新入队测试，
   不要用脚本升级前的数据作比较；记录两个 run 实际使用的 bench 提交哈希。
3. 在提交的 measurements 表中筛选 `memory-j1/module/`，按 `peak-rss-median` 的值排序找热点；
   在基线／候选比较中检查该子指标的变化，并同时检查 `peak-rss-max` 和 `elapsed-median`。
4. 按本流程的 5% RSS／10% 耗时门槛决定保留或撤回，并把结果页面、run 名、两个源码提交、
   bench 提交、runner、模块清单与原始日志路径写入每轮记录。

协议来源：[Radar bench repo specification](https://github.com/leanprover/radar#bench-repo-specification)。
远程入口另见 [PERFORMANCE.md](PERFORMANCE.md)。本节提供操作说明和脚本示例，
不表示已部署 `memory` run、发送 `!radar` 评论或上传本地测量结果。

## 每轮记录

| 轮次 | 基线／候选标识 | 模块与假设 | RSS 中位数／最大值 MiB | 耗时中位数 s | 正确性检查 | 决定 |
|---|---|---|---|---|---|---|
| 0 | 提交 + 工作区快照 | 初始基线 | 待测 | 待测 | 待检查 | 基线 |
| 1 | 提交或补丁路径 | 一个修改原因 | 待测 | 待测 | 待检查 | 保留／撤回 |

内存改善率 = `(基线 RSS 中位数 - 候选 RSS 中位数) / 基线 RSS 中位数 × 100%`。
每轮附上：
- 测量位置（本地／远程）、远程 run URL（如有）、脚本／bench 提交和 runner。
- 全仓排名依据、预期／成功模块数、排除项、本轮清单及选择依据。
- 基线／候选源码快照、JSONL、原始日志路径、目标及下游 RSS／耗时变化。
- 正确性与公理审计结果、保留／撤回理由。

最终报告全仓复核排名、疑似回退复测结论、累计改善、未解决热点和停止原因。
不得将热点子集排名写成全仓排名，或将本地 JSONL 写成已发布的 Radar 网页结果。
