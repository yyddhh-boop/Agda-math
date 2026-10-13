# DHH 陈述形式化状态：独立概念审计

本文件审计代码定义的数学范围，不把类型检查当作模型比较定理或 DHH 的证明。2026-10-12 已加入真实几何、Δ 完整性、稳定 nerve 及闭合陈述类型。历史验收回执为 **176 个模块，退出码 0，2026-10-12 13:55:35 UTC**，对应当时新增的 30 个模块。本次续接的 `HornFilling` 提供实际 `N∞-Kan` 证明项。前一轮190模块验收时间为2026-10-13 11:30:51（北京时间），回执保存在 `checks/verification-before-comparison.json`。最新整库验收为 **206 个模块，退出码 0，2026-10-13 17:02:52（北京时间）**，耗时 7.106 秒，复用已检查依赖缓存；逐文件哈希见 `checks/verification.json`。前一版201模块回执保存在 `checks/verification-before-composition.json`。`DayMonoidal`、`DayMonoidalLift` 因转换检查超时保留为未验收的历史草稿，未包含在本次迁移交付中，也不计入正式源码验收。

## 确认已经定义的内容

- `DHH.CubeCategory` 取 face、coordinate deletion、相邻 min/max 及其复合生成的具体立方体映射。它按实际 Bool 顶点函数相等识别不同 word；它没有偷偷取所有图映射 `Q m → Q n` 作 cube morphism。
- `DHH.CubicalNerve` 与 `DHH.PresheafInterop` 给出全部自然数维数的 `N₁G` 及其预层结构。
- `DHH.Realization.Coend` 给定协变的拓扑 disk diagram 后，对所有维数构造集合商及商拓扑，并证明兼容连续 disk maps 的因子性质。
- `DHH.Realization.Graph.GraphRealization E` 实际构造 `NG`、`NG-map` 和普通函子 `NG-functor`；其 `W` 是对实际 `NG-map` 应用已定义的同伦类等价条件，而不是一个任意输入的箭头谓词。
- `DHH.Topology.WeakEquivalence` 同时检查路径分支集合及每一个源基点的所有正维同伦类集合，没有只保留某个固定有限 n。
- `DHH.Localization.LevelwiseResolution` 实际定义每一维的 free resolution、marked words 的逐维局部化、face/degeneracy 及其规律。单独的 `LocalHom` 是集合；全部逐维数据组织成完整的映射单纯集以后，才是派生映射信息的候选模型。
- `DHH.Statements.Full` 把对象项和全部图对的映射项放在同一个 `DHHStatement` 类型中。映射对象来自 `DKMapping` 的全部度数及拓扑实现，比较映射来自实际的 `NG-relative`，没有把所需的映射空间或其比较映射作为任意输入。`Full` 保留通用 `E`、`S`、`E-map`；`Concrete` 已将其固定为实际实立方体、实单纯形及兼容提升。

## 2026-10-12：复合结构与函子律的独立复核

- `PresentedCategory` 的外延性确实包括自然性证明字段；它们是集合中的等式，故由命题性补全 record 路径。态射集合性与全部范畴律均有证明。
- `PresentedProducts` 不仅给逐度积和终对象，还提供 Cubical 库 `BinProduct` 和 `Terminal` 的泛性质：分解的存在与唯一性均已证明。
- `LevelFunctorLaws` 在同一原始函子上比较局部化延拓，用 `PowerFunctor` 的原始箭头规律证明两者在生成元上一致。身份与复合的方向、`suc n` 度数和固定对象函数均已核对。
- `DKEnrichment` 的复合与单位是实际 `PresentedNatural`；面、退化相容性来自逐度函子的 `F-seq`、`F-id`。左右单位和结合律是整个自然变换的等式；结合律两边使用同一个三重积定义域。相对函子保持这两种操作。
- `DKMappingFunctor` 将全部度数的恒等/复合律提升为整个诱导单纯映射的等式。`SimplicialFunctor` 在商的每个 cell 上检查对应连续映射规律；`Realization/DKMapping` 将二者连接起来。
- `Full` 使用同一具体实现的公共别名，并构造实际 `enrichedComparison`。原有两个 DHH 字段、全部图对的量词及三个显式几何参数均保持原义。

**复核边界：** 得到的是 `DeltaPresentation` 上的内部单纯富集结构；新的 `PresentationCompleteness` 已证明它与具体 Δ 互逆。没有由此证明经典 DK 比较、映射对象的 Kan 性、同伦协调 nerve 为所需 ∞ 范畴，或几何实现保持积。实现后映射空间的连续复合仍需独立工作。已有普通函子律不能充当这些定理。

## 同伦类的维数约定

`BasedCube X x n` 的参数 n 对应几何维数 n+1。因此 `Pi X x 0` 是 π₁ 的同伦类集合，`Pi X x 1` 是 π₂，依此类推。

`BasedHomotopy` 使用 n+2 维 disk：第一坐标是同伦时间，两个第一坐标端面分别是 f 和 g；`there i` 所指的全部侧面固定为基点。这符合端点固定的基于立方体同伦。

代码没有加入同伦群的乘法、逆元等代数结构。对标准实几何模型，连续映射诱导群同态，诱导的同伦类函数为双射即可表达同伦群同构的检验。现在实际形式化的是这些同伦类集合与函数；标准实几何现已具现；与经典 πₙ 的代数结构比较仍需单独证明。

## `Carrier NG` 是集合为何仍可能有高阶同伦

这里使用点集拓扑。每个拓扑空间的点载体是 hSet；`Carrier NG` 的 Agda 相等路径只表示点相等。它没有把空间的拓扑同伦论截断成 0-type。

拓扑路径另定义为连续的一维 disk map，高阶同伦用连续多维 disk maps 表达。几何实现的高维信息在 disk 的拓扑与商拓扑中；只查看最终集合商、不查看其拓扑，会失去这些信息。

## 本轮关键证明的独立复核

1. **实数立方体。** Dedekind 实数是实际 lower/upper rational cuts，含 inhabited、rounded、separated、located 条件。`RealCubeDescent` 以有理间隙的 locatedness 取有限 Boolean 近似，再按生成词归纳证明 min/max 和端点保持近似。Boolean 输出相等因而转移所有有理下界；`realLowerExt` 给实数相等。这里只决定有理数比较，不决定任意实数比较。独立复核范围为实数与下降核心；其拓扑和几何模块另由安全检查与一维同胚、端点分离检查支持。
2. **Δ 呈示完整性。** 原 WordRelation 没有加语义相等构造子。规范化在原始六族单纯关系内证明；规范形的语义单射由结构归纳证明。由此得到 `presentation-faithful`、hom 等价及严格互逆函子，已独立逐层审读并安全复查。
3. **稳定 nerve。** 已独立核对 CK §3/Proposition 3.5。第 k 层是 `Nₘ(k+1)`，第 0 次过渡用 l*，第 1 次用 r*，以后交替。逐度集合商有实际余极限泛性质；原 Boolean N₁ 与 Fin-stage1 的双向自然同构成立。`N₁→N∞` 仅为实际自然映射，不附带弱等价证明。这里是普通预层余极限，不是已证明的同伦余极限。
4. **单纯形作用。** 对 `f:[m]→[n]`，pullback 给 `Cut n→Cut m`，因此重索引给协变的 `RealSimplex m→RealSimplex n`。作用正确地把顶点 i 送到 f(i)。有限 cut 分类及有序坐标单纯形的识别见 `CutClassification` 与 `RealSimplexCoordinates`。

5. **闭合陈述。** 独立复核 `Concrete`、`Full` 和 `RealSimplexLift`，并重新安全检查 `Concrete`。三种几何均为实际构造；提升的底层映射是 `lift ∘ f ∘ lower`。全部图对、所有空间对象、所有正维与基点量词均保留；Type₁/Type₂/Type₃ 层级一致。`makeDHH` 要求两份实质证明，`DHH-isProp` 只给证明无关性，无隐藏的猜想证明。

## 递归程序与组合基础的复核（含本次续接）

- **带证明的 Δ 词判定。** 递归比较原有范式，正反两种结果都给原 `WordRelation` 商上的证书。增量复合的正确性与范畴律已核对；没有修改原关系或加入语义等式公理。仅判定有限单纯词，不判定一般图的弱等价。
- **选面子预层与粘合。** 面分解对前合成封闭；包含逐度单射。`FaceGluing` 证明全重索引相容数据的粘合与唯一性；`FaceIntersections` 将其归约到同面、反面和余维二交集，`SelectedFinitePresentation` 给出实际全维呈示同构。Boundary/OpenBox 的有限节点和关系由可判定选面算法生成；填充本身由本次 `HornFilling` 的独立构造提供。
- **Kan 定义与复合。** `IsKan` 和 `IsKanFibration` 使用截断存在；`ChosenKanFillings` 是更强的数据。恒等提升和两次提升的拼接实际构造；复合纤维化证明的两次截断消去均以命题为目标，没有选择原理。
- **整数窗口。** 整数图邻接为相等或相邻整数的命题截断。截断窗口保边，有限网格嵌入后回缩为恒等，映射延拓后限制精确恢复。固定其余坐标后，每个坐标越过窗口端点不再影响函数值；没有声称整个窗口外取同一个常值。最新 `CenteredInterval` 已接上 CK 居中/交替窗口相容性，后续完整比较见原文对齐记录。
- **共同阶段。** 有限过渡递归与 `max` 同步先处理节点，再处理全部有限生成关系。`PresentationStages` 和 `WholeBoxStages` 已提升整个有限呈示及 horn 自然变换；`PresentationEqualities` 给出两个阶段映射的后阶段等式，包含零节点情形；`PresentationComparison` 给出阶段映射商与余极限映射集合的等价。结论覆盖全部 cell 维数及无限目标图，存在性保留命题截断，不提供规范阶段搜索或任意 filtered category 的版本。
- **图实现。** `GraphPresentation` 按节点网格生成边；`GraphCoend` 对任意预层的全部网格降商，证明 Hom 等价、函子律、unit/counit 和两条三角等式，`GraphCoendAdjunction` 给出实际伴随记录。`StagedFaceGraphs` 将整个 horn 映射转换为阶段图映射；`GraphPresentationComparison` 的实际两逆图同态已通过整库安全检查。这些结论均未把 unit/counit 或 horn 阶段表示当成弱等价或 filler。
- **通用 horn 归约。** 已通过整库安全检查的 `UniversalHornReduction` 固定小图 `H=Γ_(suc k)(OpenBox missing)` 及其 unit 后接阶段包含的 horn。它证明：若每个 n、missing、k 的这个固定 horn 都有截断填充，则任意 universe 的任意图 G 都有 `IsKan (N∞ G)`。整体边界由余端求值和阶段自然性精确恢复；两次截断消去均进入截断目标，不选代表。`HornFilling.universalFill` 已给出每个固定单位 horn 的实际填充，`universalHornFillings` 成为该族的证明项，归约由此取得无条件的 `N∞-Kan`。对已给定第 k 阶段的完整 horn，`StageFilling.stageFill` 在 `tripleStage k = k + (suc k + suc k)` 层填充；对任意稳定 horn 没有选取规范阶段，也没有取得 `ChosenKanFillings`。
- **收缩操作。** `HornInterval` 已把固定距离 D 的正负 height 变成实际 `Iₘ→Iₘ` 图同态，并证明固定输入坐标时对 D 保相邻；`Padding`、`GraphResize` 的递归窗口压缩、全维自然性及恒等/复合律均已通过整库安全检查。后续 `HornWindow` 识别窗口公式，`HornGridEdges` 和 `HornFocusedMap` 给出每条输出边的共同选面证书，`HornRetraction` 将其接到任意缺面位置的实际 `Γₘ(horn)`；没有改用环境诱导子图或边的传递闭包。`HornBoundary.full-boundary` 是整个 horn 自然变换的边界等式，`StagePadding.middle-later` 识别原交替有限过渡，`middle-include` 的方向为后阶段压缩 cell 到原 cell。
- **Day 相干。** 单位子、结合子、自然性及三角形/五边形证明本体已通过整库安全检查；`DayUnitLift` 的任意 universe 单位两逆、自然性和三角形也已通过整库检查。`DayTensorCategory` 已给出实际张量函子和全 universe `TensorStr`；完整 `MonoidalCategory` 包装因转换检查超时保留为树外草稿，见 `checks/day-wrapper-diagnostics.json`。稳定图 nerve 富集自己的单位/结合律及 `NerveFunctor` 对它们的保持仍是独立义务。
- **真实几何比较。** `rawToStable` 由已有 `N₁→N∞` 和同一真实立方体余端构造，自然性逐 cell 证明。`StableKanClaim` 的任意图实例现由 `HornFilling.N∞-Kan` 提供证明项；`RawToStableWeakEquivalenceClaim` 仍无证明项，也没有作为前述构造的假设。

本批新模块的中文注释同时记录递归/消去依据、输入和输出、正确性证书、研究候选及其未证边界。最终机器检查证据仍以 `checks/verification.json` 为准；独立审读补充检查定义对应的数学含义，不以检查通过替代模型识别。

## 不能宣称已经完成的部分

1. **经典局部化模型比较。** 所有箭头包括恒等箭头作为自由生成元的 construction，与 DK 原文 non-identity free resolution 不是逐字同一个模型。经典比较定理尚未形式化。
2. **对象集合条件。** 内部 `Category` 允许非 hSet 对象类型；`ObjectBoundary` 已以提升的两点图置换证明每层 `Graph ℓ` 非 hSet。新 ordinal 编码只覆盖附带显式良序的图或整族各阶良序的预层；尚无任意对象覆盖定理。经典 O-Cat 的固定对象集合假设不能直接照搬；截断对象也不会自动下降 Hom 与复合。
3. **稳定 nerve 的弱比较。** 余极限与原文直接整数稳定预层的比较、实现比较及普通 Kan 填充已证明；`N₁→N∞` 的 anodyne/弱等价、A 群与原文 W 的识别仍未完成。`N∞-Kan` 覆盖所有 universe、无限图及全部维数，未将目标限制为有限图，也未给任意稳定 horn 的指定填充程序。
4. **原文富集与局部化源。** 已有 BOX Hom、真实 Day 张量及几何内部 Hom、Day 相干证明本体、稳定复合与单纯局部化泛性质类型；稳定富集的单位/结合、nerve 作用保持结构、几何内部 Hom 的局部 Kan 性、相干 nerve、marked Ex 实例及固定诱导映射、空间侧相干模型仍缺。稳定图 Hom nerve 的局部 Kan 性可将 `N∞-Kan` 应用于 `HomGraph G H` 取得。若保留旧候选，还需普通图局部化与原文富集源的比较。
5. **π 群与实现的乘积。** 当前同伦类定义完整覆盖所有维数；群运算及经典比较、实现后映射空间的连续复合仍需进一步证明。
6. **DHH 的证明。** 陈述类型没有 inhabitant；本任务不要求证明猜想自身，但完整原论文陈述及上述必要模型比较仍须继续完成。

真实实立方体、真实单纯形、兼容宇宙提升、Δ 呈示完整性已经关闭旧缺口。离散测试几何不用于新的闭合类型。

## 对最终双字段陈述的判定

`essentially-surjective` 取每个 `Top ℓ` 在实际 `topMarking` 的普通局部化中与某个 `NG` 的同构；`fully-faithful` 取每一对图的实际映射比较在 `E-map` 下的全维弱同伦等价。前者无需强加“存在一条单向弱等价”的额外条件，后者也没有降为 π₀ 双射。

`Statements.Concrete.DHH : Type₃` 把两项固定在同一套已构造实几何上，是真正闭合的命题类型。图与空间点载体在 Type₁，局部化映射空间在 Type₂；所有图对与全部维数的量词都保留。`DHH-isProp` 证明命题性，`makeDHH` 仅把两份所需证明打包，不提供任何一项证明。

把该全箭头自由分辨版本精确识别为原文的 ∞ 范畴等价，仍依赖上列模型比较。不能把这些未证比较藏进“基础设施全部完成”的结论。

## 最终报告的准确表述

可以说：“已给出实际实几何、全部维数、实际映射比较的闭合 DHH 陈述类型，并安全检查；原文模型的最后比较仍未全部形式化。”

可以另说：“实际交替余极限 `N∞` 已有普通 `IsKan` 的安全检查证明项；有限阶段 horn 具有明确三倍网格填充。”

不能说：“经典 DK ∞ 局部化泛性质、`N₁→N∞` 的弱等价、原文富集源比较均已证明”“任意稳定 horn 已有 `ChosenKanFillings`”或“DHH 已证明”。

## 原文对齐批次的独立审查

详细构造与来源见 [原论文模型对齐记录](original-paper-alignment.zh.md)。只读独立审查包括：图 Hom 的 BOX 闭结构；几何 tensor 与次数分块；单纯内角、E¹ 参数对象、指数及标记的定义；Definition 3.6 的实际限制自然变换与明确 universe 量词；对象非集合回路；连续同构的余端消去与基点回拉。整数逐方向稳定、生成算子的原文对应也做了来源核查。

机器检查和独立审查分别记录：Agda 检查所有定义与证明项，来源核查检验数学对象是否正是所称模型。源码程序标注递归参数、商/截断消去范围与相容义务；没有把“可表达”解释为“可判定”，或把准范畴泛性质类型解释为已有局部化实例。
