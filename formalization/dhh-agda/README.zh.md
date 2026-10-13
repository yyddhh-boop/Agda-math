# DHH 的 Agda 陈述与基础设施

本项目把 DHH 所需的组合对象、全维拓扑实现、弱等价和局部化分辨写成可检查的代码。已构造真实的 Dedekind 实数立方体、实单纯形及兼容的宇宙提升；本次续接又证明实际交替余极限 `N∞` 的普通 Kan 性，并保留 **没有几何参数的闭合陈述类型**：

```agda
-- DHH/Statements/Concrete.agda
DHH : Type₃
DHH = Geometric.DHHStatement
```

这同时要求每个空间有图模型、每一对图的完整映射比较为全维弱同伦等价。没有提供 `DHH` 的 inhabitant，也没有把当前全箭头自由分辨与原文局部化模型的比较算作已经证明。因此，“闭合且可检查的陈述类型”已经有了；“原论文所有模型识别均已形式化”还没有全部完成。

每个正式模块启用 `--cubical --safe`，没有 `postulate`、证明洞或绕过检查的选项。历史验收回执为 **176 个模块，退出码 0，2026-10-12 13:55:35 UTC**，对应当时新增的 30 个模块。本次续接的 `HornFilling` 提供实际 `N∞-Kan` 证明项。前一轮190模块验收时间为2026-10-13 11:30:51（北京时间），回执保存在 `checks/verification-before-comparison.json`。最新整库验收为 **217 个模块，退出码 0，2026-10-13 20:43:18（北京时间）**，耗时 147.765 秒，复用已检查依赖缓存；逐文件哈希见 `checks/verification.json`。前一版206模块回执保存在 `checks/verification-before-enrichment-associativity.json`。本轮新增11个稳定结合律、Day参数求值与内部Hom基础模块；见 `docs/enrichment-continuation.zh.md`。`DayMonoidal`、`DayMonoidalLift` 因转换检查超时保留为未验收的历史草稿，未包含在本次迁移交付中，也不计入正式源码验收。

## 阅读入口

先读 `docs/original-paper-alignment.zh.md`（原文模型及未完成接口）和 `docs/DHH陈述与基础设施导读.zh.md`，再读 `DHH/Statements/Concrete.agda` 和 `Full.agda`。独立范围审查见 `docs/statement-status-audit.zh.md`；具体模型义务见 `docs/realization-foundations-audit.zh.md`。第一批图例子和历史文献说明保存在 `docs/first-foundations.zh.md`，其中“尚未实现”的状态属于第一批快照。

## 后续研究取向

按用户 2026-10-12 的明确要求，优先从算法、递归、结构归纳、自然性及泛性质寻找 DHH 的统一构造机制。小例子枚举用于直觉与反例，不以扩大穷举规模作为研究主线。源码已标注输入/输出、递归或消去依据、保持规律及计算边界；阅读地图与候选结构问题见 `docs/DHH陈述与基础设施导读.zh.md` 第 11 节。区分实际可计算的构造、带正确性证明的操作、命题截断的存在性和无限对象的泛性质，保留原始完整 DHH 的量词。

## 实际构造的各层

| 层 | 模块 | 内容 |
|---|---|---|
| 图 | `Graph`、`GraphSets`、`FinitePath`、`Homotopy` | 自反无向图、允许压边的映射、BOX、有限路径与变形链、普通图范畴；允许无限顶点图。 |
| 全维立方预层 | `CubeCategory`、`CubicalNerve`、`PresheafInterop` | 面、退化、相邻 min/max connections 生成的具体立方范畴；全部维数的 \((N_1G)_n=\mathrm{Gra}(Q_n,G)\)；预层、自然变换、函子及 representable/Yoneda 分类。 |
| 拓扑 | `Topology/Base`、`Basis`、`BasisConstructions`、`FinitePowers`、`IndexedProduct`、`BasisLift` | 点集拓扑、连续映射、商拓扑、小拓扑基、乘积与子空间、基拓扑的宇宙提升；不假设 resizing。 |
| 实几何 | `Geometry/RealCubeDiagram`、`RealCubeLift`、`RealSimplex`、`RealSimplexLift` | 实际 Dedekind 实数、通常区间基、全部维实立方体与有序坐标单纯形，连续算子及函子律，同一几何的兼容提升。 |
| 稳定 nerve | `StableNerve/*` | 所有有限网格的 Nₘ、左右交替过渡、集合层序列余极限 N∞；已证与原文直接整数稳定预层自然同构、实现具有连续逆及全维弱比较。本次 `HornFilling.N∞-Kan` 已证明任意 universe、任意无限图及全部维数的普通 Kan 性；N₁→N∞的弱等价仍缺。 |
| 全维实现 | `Realization/Coend`、`Realization/Graph` | 给定拓扑 disk diagram，实际构造所有维 cell 的不交并、粘接关系、集合商及商拓扑；证明 coend 普遍性质，构造 \(NG\) 与其函子。 |
| 全维 W | `Topology/WeakEquivalence`、`Statements/RelativeRealization` | 路径分支；任意正维的边界固定 cube maps 及同伦类；诱导函数；同时检查 \(\pi_0\)、所有源基点及所有正维的 W；恒等与复合封闭；实际相对实现函子。 |
| 普通局部化 | `Localization/Zigzag`、`Ordinary`、`OrdinaryEvaluation`、`OrdinaryFunctor` | 真实 zigzag、生成关系和商范畴；W 成为同构；普通函子的延拓、唯一性与局部化函子性。 |
| 高阶分辨 | `Localization/FreeCategory`、`ResolutionOperators`、`RelativeFree` | 自由范畴 F、ε、δ 及 comonad 规律；全位置的面、退化与六族单纯恒等式；逐生成元 W 的自由标记。 |
| 单纯形语言 | `Simplicial/Ordinal`、`Presentation`、`Presented`、`PresentedCategory`、`PresentedProducts` | 具体 Δ 与生成关系的商呈示；全部 ordinal maps 的分解；规范形给出呈示的满忠实性和具体 Δ 的互逆函子；呈示单纯集的实际范畴、终对象与积。 |
| 派生映射构造 | `Localization/DKMapping`、`LevelFunctorLaws`、`DKMappingFunctor`、`DKEnrichment` | 全度映射单纯集；相对函子作用的恒等与复合律；映射单纯集之间的复合、单位、结合律及保持律；实际内部单纯富集范畴与比较函子。当前分辨与经典 DK 模型的识别仍需证明。 |
| 实现的函子性 | `Realization/SimplicialFunctor`、`Realization/DKMapping` | 商拓扑实现成为实际函子；相对函子诱导连续映射，并保持恒等与复合。`Full` 使用这套公共构造。 |
| 完整陈述框架 | `Statements/Objects`、`Statements/Full`、`Statements/Concrete` | 将对象本质满性与所有图对的派生映射弱等价写成一个待证类型；不提供该类型的证明。 |
| 例子 | `BoundaryChecks`、`Examples`、`NerveExamples`、`Realization/Examples` | BOX 对角线反例、方块扩张障碍、四边环图同伦收缩；单点图的全部维数实现可缩。 |

普通局部化只给态射集合，不能单独记录映射之间的高阶同伦；全部逐维分辨与面、退化共同组织，才提供高阶派生映射数据。`Cell₂` 是辅助二维生成展示，`HoGraph` 是普通有限链同伦范畴，两者均不能替代完整 DHH。

本轮补齐的关键结构是：对所有对象 x、y、z，候选映射单纯集有实际的 `Map(x,y) × Map(y,z) → Map(x,z)`，并与所有面、退化相容；单位与结合律是整个单纯映射的等式。`Full.enrichedComparison` 实际证明由 NG 诱导的比较保持这些操作。这个内部富集结构没有附带映射对象的 Kan 性，也没有给出经典局部化泛性质。几何实现后的映射空间连续复合仍需实现与积的相容性，不能由“实现是函子”自动推出。

## 新增的递归构造与基础定理

- `Simplicial/DecidableWords`、`NormalizedComposition`：有限 Δ 词的带证明相等判定、增量规范化及范式的范畴复合律。
- `Cubical/Faces`、`FaceGluing`、`FaceIntersections`、`FiniteFaceIndices`、`SelectedFinitePresentation`：实际边界/open box 子预层，所有重索引交集归约到有限余维二关系，及其全维有限呈示同构。
- `Cubical/Kan`、`KanComposition`：普通填充存在性与指定填充程序的区别，恒等和复合纤维化的实际提升证明。
- `StableNerve/IntegerInterval`、`IntegerClamp`：整数网格、有限窗口嵌入与回缩、有限图映射的无限网格延拓及限制恢复。
- `StableNerve/StageArithmetic`、`CommonStage`、`FiniteStages`、`StableStages`：递归阶段过渡、余极限相等的共同阶段刻画，以及实际稳定神经中有限族的共同阶段表示。
- `StableNerve/PresentationStages`、`PresentationEqualities`、`PresentationComparison`、`WholeBoxStages`：整个有限呈示及 horn 自然变换的阶段因子化、后阶段等式，以及阶段映射商与余极限映射集合的等价；阶段存在保留命题截断，目标图允许无限。
- `Cubical/GraphPresentation`、`GraphCoend`、`GraphCoendAdjunction`、`StableNerve/StagedFaceGraphs`：按生成网格的边粘接图，构造实际 `Γₘ ⊣ Nₘ`，把整个 horn 映射解释为阶段 horn 图映射。`GraphPresentationComparison` 的两种图实现同构已通过整库安全检查通过。
- `StableNerve/HornDistance`、`HornWindow`、`HornGridDistance`、`HornGridEdges`、`HornFocusedMap`：递归窗口/距离规则、所有输出边的共同选面证书与首坐标收缩。
- `StableNerve/GridFocus`、`HornFaceEvaluation`、`HornSelectedEvaluation`、`HornRetraction`、`HornBoundary`：任意缺面位置的实际生成 horn 图映射，以及整个 horn 自然变换的精确边界等式。
- `StableNerve/StagePadding`、`HornFilling`：`m = suc k` 时在 `tripleStage k = k + (suc k + suc k) = 3k + 2` 层使用三倍网格；`middle-later` 识别原交替 `laterMap`，`middle-include` 恢复原余极限 cell，`StageFilling.stageFill` 给出有限阶段 horn 的实际填充。
- `StableNerve/UniversalHornReduction`、`HornFilling`：`universalFill` 已填入原通用接口，`universalHornFillings` 是实际证明项；结合整个 horn 的截断阶段提升，得到 `N∞-Kan : {ℓ : Level} (G : Graph ℓ) → IsKan (N∞ G)`。
- `StableNerve/GeometricComparison`：实际原神经到稳定神经实现的连续比较、自然性，以及两个尚未证明的基础比较陈述。

这些模块的中文注释说明输入、递归/消去依据、保持的不变量、程序与证明的关系及适用边界。详细阅读见 `docs/finite-presentation-stage-lifting.zh.md` 和 `docs/horn-retraction-algorithm.zh.md`。稳定 nerve 的 Kan 证明已通过最新217模块整库安全检查，回执见 `checks/verification.json`。任意稳定 horn 的阶段表示仅为命题截断，故结论是普通 `IsKan`，未给出 `ChosenKanFillings`。`N₁→N∞` 的弱等价仍未证明。

## 原文模型对齐的新构造

历史验收批次的 `IntegerCubical` 给出有限网格余极限与原文直接整数稳定 nerve 的完整自然同构；`IntegerRealization` 给出其连续逆及全维弱比较。`DayTensor`、`DayClosed` 实际构造几何张量及内部 Hom，`StableComposition` 给出稳定张量复合，`NerveFunctor` 给出图 nerve 的 Hom 作用。后续 Day 单位子、结合子、自然性及三角形/五边形相容的数学本体已通过整库安全检查；`DayUnitLift` 的任意 universe 单位两逆、自然性及三角形也已通过整库检查。`DayTensorCategory` 的实际张量函子及全 universe `TensorStr` 已验收；完整 `DayMonoidal`、`DayMonoidalLift` 库记录包装仍是未验收历史草稿，未包含在本次迁移交付中。这不代替稳定富集自身的单位/结合律。`LocalizationUniversal` 展开原 Definition 3.6 的整个函子准范畴泛性质类型；它尚不是一个局部化实例。

`ObjectBoundary.Graph-not-set` 已证明每层图对象类型非集合，需要全对象编码或内部模型比较；这不否定 DHH。新 `OrderedGraphCodes`、`OrderedCubicalCodes` 的覆盖要求输入显式良序，不能据此替代任意图或任意预层的量词。完整原论文陈述尚缺相干 nerve、几何内部 Hom 的局部 Kan 性、标记局部化实例、原 W 与空间模型的识别；图的稳定 nerve 的 Kan 性已由 `N∞-Kan` 关闭。`NerveFunctor` 特定求值的共同阶段/curry β 附属草稿仍未通过检查，已移出 DHH 源码；它不同于已完成的一般有限呈示阶段定理。详细记录见 `docs/original-paper-alignment.zh.md`、`checks/original-paper-alignment.json`。

## 本轮后续验收

最新整库验收为 **217 个模块，退出码 0，2026-10-13 20:43:18（北京时间）**，耗时 147.765 秒，复用已检查依赖缓存；逐文件哈希见 `checks/verification.json`。前一版206模块回执保存在 `checks/verification-before-enrichment-associativity.json`。本轮新增11个稳定结合律、Day参数求值与内部Hom基础模块；见 `docs/enrichment-continuation.zh.md`。 从190模块版本起先新增11个基础模块，随后新增5个复合与单位基础模块；严格保留的缺口见 `docs/stable-enrichment-and-transition-progress.zh.md`。保留前一轮12份历史草稿，另有16份本轮未验收候选与替代草稿移出正式源码，并单独保存在 `research-drafts/unverified`，不计入验证，也未算作已证明。

## Carrier 是集合为何仍有高阶同伦

这是点集拓扑表达：`Carrier X` 的 Agda 相等表示点相等，拓扑路径另由连续区间映射表达，高阶同伦由连续多维 cube maps 表达。高维信息保存在每个 disk 的拓扑及商拓扑中，不能只看底层集合商。

内建 Cubical Agda 的 `I`、有限图 \(I_m\) 和拓扑实区间 \([0,1]\) 是三个不同对象。内建 Kan 运算不能证明原始 \(N_1G\) 为 Kan；CK 的 \(N_\infty\) 是另一个构造。[CK §3](https://arxiv.org/html/2202.03516v3)

## 原始 DHH 的剩余基础义务

已关闭的旧缺口包括：真实 `[0,1]^n` 的几何实例、实际单纯形及算子、两个 universe 的兼容基拓扑提升、生成元与关系确实完整呈示 Δ。`RealCubeChecks` 还证明一维立方体与实闭区间同胚、两个端点不同。`DiscreteCubes` 保留为工程反例测试，不参与 `Concrete.DHH`。

仍待形式化的模型比较包括：

1. 内部对象类型与经典对象集合模型的衔接。若还要识别旧候选，另需全箭头自由分辨与经典 DK 局部化的比较。
2. `N₁ → N∞` 的弱等价及原文 A 群/W 识别。稳定 nerve 的普通 Kan 性、交替有限网格余极限与直接整数稳定预层的自然同构及实现比较已证明。
3. 稳定立方富集的单位/结合律、nerve 作用保持这些结构、内部 Hom 的局部 Kan 性，以及原文同伦相干 nerve、marked Ex 局部化和固定诱导映射、空间侧相干模型。若要识别旧候选，还需普通图局部化与这一源的比较。
4. 连续立方体同伦类的经典 π 群识别及群运算；实现后映射空间的连续复合还需要实现与积的比较。

这些是完整原论文陈述所需的基础模型证明义务，仍在本任务范围内。DHH 的对象实现性与所有映射比较等价本身没有提供证明；用户不要求证明猜想自身。

文献版本固定为 [CK 2202.03516v3](https://arxiv.org/html/2202.03516v3)、[强猜想 2306.02218v1 §12–14](https://arxiv.org/pdf/2306.02218v1)、[Dwyer–Kan §2、§4](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-1.pdf)。固定有限 n 的结果不能代替完整 DHH。

## 复现

Agda `2.8.0-3d04bac`；vendored Cubical 0.9，commit `b150186d2544e7efeddd31e5d14a8b9ecbb100f7`。运行：

```sh
python3 check.py
```

脚本递归审查本项目全部源码并检查 `Everything.agda`，将版本、退出码、耗时和逐文件 SHA-256 写入 `checks/verification.json`，输出见 `checks/latest.log`。最终编译状态以 manifest 为准。

库的 `UnsupportedIndexedMatch` 提示涉及部分 transport 计算限制；没有允许证明洞或关闭安全检查。[Agda 官方说明](https://agda.readthedocs.io/en/latest/language/cubical.html#indexed-inductive-types)
