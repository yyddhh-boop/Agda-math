# 稳定模型、阶段过渡与闭伴随：本轮验收

当前正式入口 `Everything.agda` 覆盖217个模块，全部通过 `--cubical --safe`。逐文件哈希、编译器与时间见 `checks/verification.json`；历史190模块回执保存在 `checks/verification-before-comparison.json`。所有图大小及全部维数保留，没有加入 postulate、证明洞或不安全绕过。

## 本轮新增的已验收模块

| 模块 | 已验收内容 |
| --- | --- |
| `Cubical/KanTransport` | 沿实际自然回缩和自然同构运输整个horn填充，保留截断存在；两个独立宇宙。 |
| `StableNerve/IntegerKan` | 对原文直接整数稳定预层给出普通Kan证明；任意宇宙、无限图及全部维数。 |
| `Enrichment/StableKan` | 实际BOX同态图的稳定nerve及整数模型为Kan；源、目标图可在不同宇宙。 |
| `Enrichment/GridCompositionCoherence` | 有限网格复合的实际单位与结合式，包含确切的网格unitor/associator作用。 |
| `StableNerve/TransitionMonomorphism` | 左右collapse的图section、任意维阶段过渡及有限laterMap/advanceCell的单射性。section不保持两个指定端点，不能充当天然逆。 |
| `StableNerve/TransitionExpansion` | 原文λ/ρ对齐的BOX局部扩张及时间起止面等式；时间只改变特殊坐标。 |
| `Cubical/DayClosedParameter` | 实际闭伴随的评价β、uncurry单射及完整参数预复合相容；四个独立宇宙。 |
| `Cubical/DayHomEvaluation` | 对真正的Day内部Hom构造参数求值及curry求值β。 |
| `Cubical/DayHomNestedEvaluation` | 用实际Day结合子接合两次求值，并保留三个独立坐标块的完整β等式。 |
| `Enrichment/StableCompositionIdentity` | 从提升的Day单位出发构造稳定恒等族，并证明常值恒等网格在所有原交替阶段保持恒等。 |
| `Enrichment/StableCompositionStageLaws` | 原已检同阶段复合等式的精确abstract别名；不改变原复合构造或定理。 |

Kan结论都是普通 `IsKan`；没有为任意稳定horn选择全局阶段或 `ChosenKanFillings`。`DayHom`的cell是整个 `RepresentableCube n ⊗ A → B` 自然变换，不是逐度笛卡尔指数。原稳定合并操作的左右单位律已经验收，但完整Day单位自然变换等式、任意稳定cell结合律已由后续验收关闭，完整Day结合图仍待验收。

## 授权同步后新增的已验收模块

| 模块 | 已验收内容 |
| --- | --- |
| `Cubical/DayHomCompositionCore` | 实际内部Hom恒等自然变换与复合构造；复合经两次真实Day求值及实际结合子定义，保留完整构造等式。 |
| `Cubical/DayHomCompositionMaps` | 恒等映射uncurry等式、复合求值β、复合β及恒等求值β。任意同一宇宙中的立方集及全部参数维数。 |
| `Enrichment/StableCompositionMergeCore` | 原 `mergeN∞` 的abstract包装、逐应用等式和同阶段式；只控制自动展开，不替换数学构造。 |
| `Enrichment/StableCompositionUnitStages` | 恒等网格的左右阶段同步、同阶段复合、有限网格单位式及实际includeStage自然性；源网格参数明确。 |
| `Enrichment/StableCompositionMergeUnits` | 原 `mergeN∞` 对任意稳定商cell的左右单位律；使用命题商消去，不选择稳定代表。 |

本批整库回执为206模块、退出码0；此前201模块回执保存在 `checks/verification-before-composition.json`。这些结果覆盖任意宇宙ℓ中同一ℓ的任意图（允许无限图）、所有维数。它们不单独提供整个富集范畴或内部Hom的完整相干模型。

## 尚未验收或未完成

12份未验收源码（10份当前候选和2份替代实现）保存在 `research-drafts/unverified`（`.agda.txt`）。它们包括完整Day单位等式、稳定结合律、神经函子保持式和内部Hom参数相容律；不计入206模块验收。诊断见 `checks/comparison-development-diagnostics.json`。正式Core中只有已检查的原合并操作包装；Day复合扩展的超时尝试单独保留。

原始 `N₁→N∞` 的 anodyne 性与标准拓扑全维弱同伦等价仍未证明。尚需所有其余面因子分解、退化和connections交叠的真实horn附着pushout、cellular饱和及其到既定真实几何实现的桥接。局部扩张采用时间首坐标，还需与原文时间末坐标写出精确图坐标识别，不能默认立方范畴允许任意置换。

此外仍需原文A群/W识别、几何内部Hom的局部Kan性、相干nerve、标记局部化、全对象编码或内部模型比较及空间侧模型。DHH本身没有证明；本任务并不要求证明猜想。

[原文公式对照：Carranza–Kapulkin，2202.03516v3，§4](https://arxiv.org/html/2202.03516v3)。本轮只关闭上表明确列出的义务。

## 原文陈述目标续接

最新217模块整库检查退出码0。新增11个正式模块关闭稳定cell结合律、完整参数求值图以及内部Hom外延性/坐标相容。完整富集实例与原文相干nerve/局部化仍未构造；详见 [本轮续接](enrichment-continuation.zh.md)。前面206模块/12草稿计数为历史批次；本轮另保存16份未验收候选，不计入正式模块。
