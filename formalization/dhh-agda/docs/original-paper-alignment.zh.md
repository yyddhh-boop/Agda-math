# 原论文 DHH：模型对齐与陈述边界

这里的“原论文”指 Carranza–Kapulkin–Lindsey 的 [Calculus of Fractions for Quasicategories，2306.02218v1](https://arxiv.org/pdf/2306.02218v1)，特别是 §12、§14 和 Conjecture 14.3。稳定图 nerve 的定义和比较另见 Carranza–Kapulkin 的 [2202.03516v3，§3–4](https://arxiv.org/html/2202.03516v3)。两篇论文的同号定义不能混引。

**当前已有闭合的候选 `Concrete.DHH : Type₃`；原论文版本还没有全部闭合。** 之前把剩余工作概括为“一个比较定理”过于简略：这包含稳定 nerve、富集、相干 nerve、标记局部化以及基础对象编码几个不同的接口。整数稳定 nerve 的自然比较已证明；后续又补出整个 horn 的有限阶段因子化、图 coend 伴随，以及几何张量的三角形和五边形相容。历史验收回执为 **176 个模块，退出码 0，2026-10-12 13:55:35 UTC**，对应当时新增的 30 个模块。本次续接的 `HornFilling` 提供实际 `N∞-Kan` 证明项。前一轮190模块验收时间为2026-10-13 11:30:51（北京时间），回执保存在 `checks/verification-before-comparison.json`。最新整库验收为 **217 个模块，退出码 0，2026-10-13 20:43:18（北京时间）**，耗时 147.765 秒，复用已检查依赖缓存；逐文件哈希见 `checks/verification.json`。前一版206模块回执保存在 `checks/verification-before-enrichment-associativity.json`。本轮新增11个稳定结合律、Day参数求值与内部Hom基础模块；见 `docs/enrichment-continuation.zh.md`。`DayMonoidal`、`DayMonoidalLift` 因转换检查超时保留为未验收的历史草稿，未包含在本次迁移交付中，也不计入正式源码验收。

## 1. 原论文的目标到底是哪条箭头

原文先把图范畴富集为立方范畴：

\[
\underline{\mathrm{Graph}}(G,H)=N\operatorname{hom}_{\otimes}(G,H).
\]

`hom⊗(G,H)` 的顶点是图映射，两顶点相邻表示这些映射逐点相邻。`N` 是整数网格上逐方向最终常值的稳定立方 nerve。它不是本项目最初的单位网格 `N₁` 的点集拓扑实现。

然后令

\[
X=N_\square\underline{\mathrm{Graph}},\quad
L=\operatorname{Ex}^{\mathrm{op}}_+(X,W),\quad
Y=N_\square\mathrm{Kan}_\square.
\]

`N□` 在这里是立方范畴的同伦相干 nerve，结果是单纯集合。`W` 标记原文 Definition 12.7 的图弱等价。目标立方 Kan 范畴的态射对象是几何张量积的内部 Hom `homL`。

Conjecture 14.3 要求由图 nerve 导出的固定映射

\[
\bar N:L\longrightarrow Y
\]

是准范畴等价。它同时比较对象与完整映射空间，不能用普通局部化泛性质或同伦范畴等价替代。

原文 §14 的局部化单位标签与 §8–9 的右分式公式不一致；实现右分式路线时应依据 Theorem 9.6(2) 使用 `min*`，不能只复制该处 `max*` 标签。

## 2. 已经实际证明的稳定模型比较

`CenteredInterval` 按阶段交替向左、向右增长，给出居中的整数窗口和逐坐标 clamp 回缩。`IntegerStable` 利用商中共同阶段判据，证明余极限 cell 与有限窗口稳定整数映射互逆。

`IntegerPaperStability` 再证明有限窗口条件与原文逐方向条件等价：每个坐标的正、负方向允许不同阈值；对有限的 `2n` 个阈值使用有限截断消去，算出一个共同居中窗口。这里没有使用可数选择，也没有从一个截断存在性中选出规范代表。

`IntegerCubical` 将逐阶等价提升到**真正的预层自然同构**：

\[
N_\infty G\cong N_{\mathbb Z}G.
\]

它不仅运输结构，还识别直接公式：面在稳定方向阈值取值，退化删去整数坐标，connections 合并相邻坐标的 min/max；任意生成词通过结构递归作用。面由唯一的最终常值定义，可对任意合法论文阈值证明公式，不要求选取最小阈值。原文 connection 数字标签的约定与源码中的 `minW/maxW` 名称须按操作本身对应。

`Realization/CubicalIso` 和 `StableNerve/IntegerRealization` 证明上述自然同构的几何实现具有连续逆；`Topology/ContinuousIsoWeak` 进一步给出所有基点、所有正维同伦类和连通分支上的等价。基点回拉明确使用 `g(f x)=x` 的路径，未将它当成定义等式。

**范围：** 上述自然同构和实现比较识别两种稳定模型。`N∞` 的 Kan 性已由独立的 `HornFilling.N∞-Kan` 证明：收缩实际保边，整个 horn 边界精确恢复，并与原交替阶段过渡相容；它不是仅由上述同构推断而来。`N₁→N∞` 的弱等价仍是待证类型。

## 3. 几何富集的实际基础

`GraphHom` 和 `GraphHomCoherence` 构造 BOX 内 Hom、评价、图层 curry/uncurry 及实际单位/结合图。

`TensorCategory` 按有限生成词递归拼接坐标块，再用语义等式消去词见证。`DayTensor` 是真正的集合余端商；其生成元包括两个维数、两个 cell 和一个立方重索引。配对的维数是 `p+q`，而不是同一维度上的笛卡尔积。

`DayTensorFunctor` 给出实际双变量函子。`DayClosed` 构造

\[
\operatorname{DayHom}(A,B)_n
=\operatorname{Nat}(\square[n]\otimes A,B)
\]

及完整 curry/uncurry 伴随等价。

`CubicalComposition`、`StableComposition` 把图映射的逐点复合接到有限网格，再按共同 `max` 阶段同步，证明阶段无关并两变量降商，得到实际稳定 Day 复合。后续 `DayUnit`、`DayAssociator`、`DayCoherence`、`DayPentagon` 已构造张量单位子、结合子、自然性和三角形/五边形，并已通过整库安全检查；`DayUnitLift` 进一步通过任意 universe 的单位两逆、自然性和三角形单项检查。`DayTensorCategory` 的实际张量函子及全 universe `TensorStr` 已验收；完整 `DayMonoidal`、`DayMonoidalLift` 库记录包装仍为未验收的历史草稿，未包含在本次迁移交付中。稳定合并的任意cell单位/结合律已完成；完整Day图式和nerve作用保持这些结构仍需证明。

`NerveFunctor` 给出实际自然变换 `N∞HomGraph(G,H)→DayHom(N∞G,N∞H)`、稳定求值及其任意稳定 cell 配对公式；有限分块求值已证等于原图 evaluation 的复合。额外的共同阶段/curry β 历史草稿没有通过最终检查，未包含在本次迁移交付中，不计入验证模块或已证结论。这是该求值作用的特定义务，不同于现已完成的一般有限呈示阶段定理。

## 4. 已展开的准范畴与局部化条件

`Simplicial/Sets` 是集合值 Δ 预层；`Horns` 给出包含全部退化的实际 horn 子预层；`Quasicategories` 精确量化全部内角。`WalkingIsomorphism` 是原文的 `E¹`，不与另一个有限参数对象 `J` 混同。

`Equivalences` 给出两个准范畴之间的 `E¹` 同伦逆条件。`Products`、`Exponentials`、`ExponentialFunctor` 实际构造函子单纯集合及预合成。`Marked` 和 `FullSubcomplex` 给出把标记边送为可逆边的整个函子子复形。

`LocalizationUniversal` 实际构造限制自然变换

\[
u^*:Q^L\longrightarrow\operatorname{Fun}_W(X,Q)
\]

并展开原文 Definition 3.6 的条件：对于每个测试目标准范畴，这条限制映射为准范畴等价。代码将测试目标的 universe `κ` 显式固定，没有将跨全部 universe 的量词藏进一个有限 `Type` 层级。

这是完整的泛性质**陈述类型**，没有为任何图局部化候选提供该性质的证明，也没有构造 `Exop+`。

## 5. 原文接口的当前状态

| 接口 | 当前精确状态 |
|---|---|
| 稳定 nerve 的 Kan 填充 | 已关闭。`HornFilling.StageFilling.stageFill` 实际填充给定阶段的整个 horn；`universalFill` 与 `universalHornFillings` 接上原归约，得到任意 universe、任意无限图及全部维数的普通 `IsKan (N∞ G)`。任意稳定 horn 的阶段表示保留截断，未提供 `ChosenKanFillings`。 |
| `N₁→N∞` 及原文 A 群弱等价标记 | 固定比较映射和全维弱比较类型已有；对应证明与 A 群识别未完成。 |
| 立方富集与 `N□Graph` | Hom、Day 张量及其相干证明本体、几何内部 Hom、稳定复合已有；`N∞HomGraph(G,H)` 的局部 Kan 性由 `N∞-Kan` 取得。任意稳定cell的结合律已完成；完整Day单位/结合图、nerve作用保持结构、几何内部Hom的Kan性及完整相干nerve尚缺。 |
| `Exop+` 与固定诱导映射 | 泛性质已展开；原文 marked Ex 的实际构造及其应用实例尚缺。 |
| 空间侧模型 | 真实拓扑几何已构造；`N□Kan□` 的完整实例及 B.20 的模型比较尚缺。 |
| 旧候选与原文源的比较 | 经典 DK 与旧全箭头分辨、普通局部化与富集相干源的比较尚缺；走原文直接路线不必先解决所有旧候选比较。 |
| 经典对象集合与内部类型 | `ObjectBoundary` 证明任意固定 universe 的 `Graph ℓ` 非集合。新 ordinal 编码的对象类型为集合，但覆盖要求显式良序输入；任意图/预层的全对象比较仍需落实。 |

`ObjectBoundary` 的两点离散图置换产生非平凡路径，并无 resizing 地提升到每个 universe，涵盖现有闭合候选的 Type₁。它不否定 DHH，只说明无公理 Cubical Agda 中的图对象类型不能直接充当经典 nerve 的对象集合。`OrderedGraphCodes` 只编码附带指定良序的图，`OrderedCubicalCodes` 要求整族指定的各阶良序；两者均没有为任意集合选良序。把对象取集合截断后，依赖对象的 Hom 和复合也不会自动下降。

## 6. 下一条结构研究路线

有限生成的面重叠判据现已构造：同一面的两种表示用 delete/insert 互逆比较；同坐标相反端点排除交集；不同坐标的重叠通过共同余维二面分解。`SelectedFinitePresentation`、`PresentationStages` 与 `WholeBoxStages` 已将节点和关系同步接到整个 open box；`PresentationEqualities` 和 `PresentationComparison` 还给出后阶段等式及 Hom 与序列余极限的比较。

`GraphPresentation`、`GraphCoendAdjunction`、`StagedFaceGraphs` 给出阶段图解释与实际 `Γₘ⊣Nₘ`；两种图实现的 `GraphPresentationComparison` 已通过整库安全检查。`UniversalHornReduction` 的通用归约现已接上 `HornFilling.universalFill`：`Type₀` 中每个按维数、缺面、阶段索引的通用 `Γₘ(horn)` 单位 horn 都有实际填充，由此推出任意 universe、任意无限目标图的稳定 Kan 性。整个 horn 的阶段表示仍是截断存在，所以最终结论是普通 `IsKan`。

本次已构造扩大网格到 horn 生成图的保边映射及完整边界等式。`HornWindow`、`HornGridEdges`、`HornFocusedMap` 给出窗口公式和共同选面证书；`GridFocus`、`HornSelectedEvaluation` 与 `HornRetraction` 覆盖任意缺面位置；`HornBoundary.full-boundary` 覆盖整个子预层的所有重索引。`StagePadding` 取 `m = suc k`、`tripleStage k = k + (suc k + suc k) = 3k + 2`，后阶段网格边长恰为 `3m`；`middle-later` 比较的是原序列的实际交替 `laterMap`，`middle-include` 证明压缩表示恢复原稳定 cell。下一步的模型义务是 `N₁→N∞` 的弱等价、A 群/W 识别以及尚未关闭的富集与局部化比较。详见 [有限呈示阶段提升](finite-presentation-stage-lifting.zh.md) 和 [horn 收缩算法](horn-retraction-algorithm.zh.md)。

horn 图的边也必须由所选面生成，不能只把顶点的并取成环境网格的诱导子图。例如单位正方形的三边 horn 已含四个顶点；诱导子图会把缺失的第四边补回来。因此回缩保边必须证明相邻点的像处在共同的已选面，不能只检查它们在环境网格中相邻。

本任务仍须完成原论文陈述的实际源、目标、固定比较及必要模型定理；用户不要求证明该固定比较是等价这一猜想自身。
