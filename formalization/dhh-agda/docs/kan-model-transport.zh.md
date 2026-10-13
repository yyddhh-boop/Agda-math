> 本文涉及的Kan运输模块已纳入本轮201模块整库安全验收；权威回执见 `checks/verification.json`。

# 稳定 Kan 性的模型运输与局部实例

本次新增的三个模块把已有 `HornFilling.N∞-Kan` 接到已有的原文整数预层比较，并给出图 Hom 的局部实例。编译验收以本次 `checks/verification.json` 和编译日志为准；此文不以定义或独立阅读代替类型检查。

## 精确证明项

| 模块 | 证明项 | 量词与结论 |
| --- | --- | --- |
| `Cubical/KanTransport` | `kanAlongNaturalRetraction` | 任意两个 universe 的预层 `A,B`，实际自然变换 `f:A→B`、`g:B→A` 以及 `g ⋆n f = id_B`；由 `IsKan A` 得到 `IsKan B`。 |
| `Cubical/KanTransport` | `kanAlongNaturalIso`、`kanAlongNaturalIsoBack` | 接受自然同构的双向自然变换及两条逆式，分别运输普通 Kan 性。 |
| `StableNerve/IntegerKan` | `transportedIntegerNerve-Kan` | 任意 universe、任意图 `G` 的中间整数预层具有 Kan 性。 |
| `StableNerve/IntegerKan` | `directIntegerNerve-Kan` | 任意 universe、任意图 `G` 的实际直接整数稳定 nerve 具有 Kan 性。 |
| `Enrichment/StableKan` | `stableHomNerve-Kan` | 两个独立 universe 中的任意图 `G,H`，`N∞ (HomGraph G H)` 具有 Kan 性。 |
| `Enrichment/StableKan` | `integerStableHomNerve-Kan` | 同一图 Hom 的直接整数稳定模型具有 Kan 性。 |

这里没有有限图限制。每个 `IsKan` 量化全部维数、任意缺面以及整个缺面子预层到目标的自然变换。

## 边界恢复与截断

输入目标 `B` 中的 horn `box`，先后合成 `g` 得到 `A` 中的 horn。`IsKan A` 只给出 `∥ OpenBoxExtension A missing (box ⋆n g) ∥₁`。已给一份实际填充数据时，`mapExtension f` 后合成填充 cell，并利用 `f` 的自然性恢复其整个边界；`changeExtensionBoundary` 再利用 `g ⋆n f = id_B`，将边界识别回原来的 `box`。

`kanAlongNaturalRetraction` 最后只用 `PT.map` 映射这份截断存在性。其输出仍然是填充的截断存在，没有从截断中抽出填充、阶段或全局选择函数，也没有得到 `ChosenKanFillings`。

整数模型的运输直接使用 `integerNerveComparison`、`integerNerveComparisonInverse` 以及已有的左右逆式。原文模型的 faces 已由最终常值端点独立定义；退化删除整数坐标，connections 为整数 `min/max`。已有 `IntegerCubical` 证明这些直接操作与运输操作在全部 cube morphisms 上相容，所以本次结论针对实际 `directIntegerNerve`，而不只是逐度的 cell 等价。

既有整数比较中也没有新增选择假设：`IntegerStable` 的窗口存在性只消去到已证明为命题的唯一比较纤维；稳定端点和直接作用只消去到唯一候选的命题纤维；有限维的 `2n` 个方向阈值以 `PT.recFin` 合并，结果仍保留截断。

## 独立核查与保留义务

另一个 Agent 对新增源码进行了独立阅读，核查了 `_⋆n_` 的复合方向、两条逆式分别用于哪一方向、填充边界的恢复以及截断边界，未发现问题。这是本次所列范围的独立核查，不是外部同行评审。

图 Hom 的局部 Kan 性来自对实际 `HomGraph G H` 应用通用定理。它不是几何内部 `DayHom (N∞ G) (N∞ H)` 的 Kan 性，也不使 `nerveHomMap` 自动成为弱等价。本次运输与局部实例不证明 `N₁→N∞` 的弱等价、原文弱等价类的识别、相干 nerve、DK 局部化模型比较或完整 DHH。
