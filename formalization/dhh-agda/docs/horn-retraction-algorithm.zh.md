# 三倍网格到 horn 的递归收缩与 Kan 填充

这一页记录已实现的收缩、完整边界等式与稳定阶段比较。`DHH/StableNerve/HornFilling.agda` 已通过 `--cubical --safe` 类型检查，实际提供 `N∞-Kan : {ℓ : Level} (G : Graph ℓ) → IsKan (N∞ G)`。结论覆盖任意 universe、无限图、任意缺面位置及全部维数。最终整库统计和源码哈希以 `checks/verification.json` 为准；历史 176 模块回执不代表本次新增源码的验收。原构造见 [CK §4.2、Lemma 4.4](https://arxiv.org/html/2202.03516v3)。

取 \(m\geq1\)、\(v\in\{0,\ldots,3m\}^{n+1}\)，缺失面为 \((i,\varepsilon)\)。设 \(c_j=\min(m,\max(0,v_j-m))\)，并令

\[
D=\sum_{j\ne i}\bigl((m-v_j)_++(v_j-2m)_+\bigr).
\]

保持其他输出坐标为 \(c_j\)。缺失端面为 1 时，特殊输出坐标可写成

\[
\Phi_i=c_i\mathbin{\dot-}(m\mathbin{\dot-}D).
\]

缺失端面为 0 时，用其反射式

\[
\Phi_i=m\mathbin{\dot-}\bigl((m\mathbin{\dot-}c_i)\mathbin{\dot-}(m\mathbin{\dot-}D)\bigr).
\]

这里 \(a\mathbin{\dot-}b=\max(0,a-b)\)。这些是实际标量程序的递归表达，`HornScalar` 给出正、负 height 对每个变量分别保相邻、有界性、零距离/大距离及反缺面边界式。已通过整库安全检查的 `HornInterval` 把固定 D 的两种 height 包装为实际 \(I_m\to I_m\) 保边图同态，并给出固定 c、相邻 D 的输出邻接证书；D≥m 时两映射等于恒等。它们一般不同时固定两个端点，所以没有包装成 `IntervalMorph`。`HornWindow` 已把压缩的数值公式与 `Padding.middleCollapse` 识别；后续网格映射、生成面评价、完整边界和原交替阶段比较也已构造。

## 保边需要共同面的见证

一次网格边只改变一个坐标 k。

1. 若 k 不是特殊坐标且 clamp 输出改变，该坐标的两次窗口外距离均为零，所以 D 不变。若 D 为零，输出在反缺面；若 D 为正，另一个坐标有正距离，它的 clamp 位于端点，给出共同选面。
2. 若这个 clamp 输出不变且是端点，k 面给共同见证，但特殊输出可能改变；这需要标量函数对 D 的保相邻引理。若不变输出是内点，来源该坐标实际上没变，按相等处理。
3. 若 k 是特殊坐标，其余坐标和 D 固定。存在其他端点时沿该共同面；其余 clamp 全是内点时 D 为零，特殊输出固定在反缺面。标量函数对 c 的保相邻引理控制剩余情形。

`HornGridEdges` 与 `HornFocusedMap.shared-face` 已实际构造这份共同面的见证。`HornSelectedEvaluation.edge` 将环境边删除共同面坐标后送入该生成面的图映射，`HornRetraction` 再搬回任意缺面位置。因此输出边属于按各面生成的实际 `Γₘ(horn)`；没有用环境诱导子图或边的传递闭包代替它。

## 两处源文字推断的修正

原文保边段落把“变化坐标的 clamp 改变”加强成其余坐标都在中间窗口，这个加强不成立。取 m=2、特殊坐标为第三个，来源 (2,0,3) 与 (3,0,3)。第二个坐标仍在窗口外；两者 D 都为 2，输出 (0,0,1) 与 (1,0,1)，由第二个端面见证相邻。

Lemma 4.4 的“位于反缺面端点便有 D=0”也不成立。取 m=2、缺失第二个坐标的 1 端面，来源 (0,0) 的 D 为 2。边界等式依然成立：此时 c_i=0，特殊输出对任意 D 都为零。

更稳的边界证明逐面处理：反缺面上特殊坐标本身就是正确端点；任一其他外端面上，其距离贡献为 m，故 D≥m、m\(\mathbin{\dot-}\)D=0，特殊输出恢复 c_i。两处修正改变的是证明推断，未据此断言论文定理或构造有反例。

## 已完成的形式化链

1. `HornScalar`、`HornInterval` 递归证明 height 的有界性、分别保相邻及零/大距离边界式；`HornDistance`、`HornWindow` 证明窗口距离规则并识别 `middleGrid` 的公式。
2. `HornGridDistance`、`HornGridEdges` 沿有限坐标递归取得正距离的坐标见证；`HornFocusedMap` 给出每个输出点的选面及每条输出边的共同面。
3. `GridFocus` 提供指定坐标与首坐标之间的实际图同构。`HornFaceEvaluation` 比较同一环境点的不同面表示；`HornSelectedEvaluation` 据此评价，`HornRetraction` 构造任意缺面位置的 `Grid (3m) (n+1) → Γₘ(horn)`。
4. `HornFocusedBoundary` 在反缺面上保持正确端点，在其他外端面上使用 `D ≥ m`；`HornBoundary.full-boundary` 先比较全部生成面，再经 Yoneda 和截断面分解消去，证明整个 horn 自然变换等于原 horn 的中间窗口细化。它包括面、退化、connections 及所有重索引。
5. `StagePadding` 证明中间窗口细化等于原交替序列的实际有限过渡；`HornFilling` 将该边界等式接到余极限包含，生成填充。

## 精确阶段与存在性边界

给定第 `k` 阶段的完整 horn 映射 `η : OpenBox missing → Nₘ (suc k) H`，设 `m = suc k`。使用

```agda
tripleStage k = k + (suc k + suc k)
```

后阶段编号为 `3k + 2`，网格长度为 `suc (tripleStage k) = m + (m + m) = 3m`，共前进 `2m` 步。`StagePadding.middle-later` 将原交替 `laterMap` 与 `changeSize (middleCollapse m)` 识别；`middle-include` 表明后阶段压缩 cell 和原稳定 cell 相同。这没有替换原过渡系统，也没有把扩大长度当作增加维数。

`StageFilling.stageFill` 返回 `OpenBoxExtension (N∞ H) missing (η ⋆n includeStage H k)`，其 filling cell 是将 `HornRetraction.Target.map` 包含到上述后阶段。`HornFilling.universalFill` 对每个实际 `Γₘ(horn)` 的单位 horn 提供未截断的填充，`universalHornFillings` 因而已有证明项；`UniversalHornReduction` 将其送入任意目标图，并合法消去 `WholeBoxStages` 的截断阶段存在性，得到 `N∞-Kan`。

明确给定有限阶段时，填充及三倍界是实际程序。任意稳定 horn 的阶段表示仍只有命题截断，最终结论是普通 `IsKan`，没有为其挑选规范阶段，也没有构造 `ChosenKanFillings`。目标图无需有限、可枚举或附带判定过程。

`N₁→N∞` 的 anodyne/弱等价、A 群与经典同伦群/原 W 的识别、原文富集与局部化模型比较及 DHH 本身仍未由此证明。小数值例子仅用于检查推断，不替代任意维数的结构证明。
