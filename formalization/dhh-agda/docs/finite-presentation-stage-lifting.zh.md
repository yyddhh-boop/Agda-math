# 从有限生成规则到整个 horn 的阶段提升

这一批工作把一个具体缺口关闭了：任意映射

\[
h:\sqcap^{n+1}_{i,\varepsilon}\longrightarrow N_\infty G
\]

都能经过某个有限网格阶段 \(N_mG\)。这里的 \(h\) 是整个立方预层的自然变换，包含所有维数的 cell；\(G\) 允许有无限顶点。阶段及因子化的存在保留在命题截断中。

## 有限的是生成规则

一个有限呈示由两份有限输入组成：节点 \(a_i\) 的维数 \(d_i\)，以及关系

\[
u_e^*a_{l(e)}=v_e^*a_{r(e)}.
\]

在来源维数 \(k\) 上，生成元是 \((i,w)\)，其中 \(w:\square^k\to\square^{d_i}\)。关系可继续沿任意立方映射前合成。按这些关系取集合商，便得到所有维数的预层。

这给出一个程序式理解：有限规则描述一个可在任意维数上调用的构造。它并不要求把无限的 cell 一一列出。代码 `FinitePresentation` 实际构造这个商，证明重索引和函子律，再证明“给节点赋值并满足关系”唯一决定整个自然变换。

## 为什么几个面交集就够了

选面复形由有限个面生成。两个重索引的面可能发生三种情况：同一个面、相反的两个面、两个不同坐标的面。

- 同一个面：面映射单射，重合来自参数重合。
- 相反面：同一坐标不能同时等于两个不同端点，交集不存在。
- 不同坐标：任意重合都经过它们的余维二交集。

`FaceIntersections` 证明这三种归约；`FiniteFaceIndices` 递归枚举坐标对并筛出选中面；`SelectedFinitePresentation` 构造选面复形与有限呈示之间的双向自然映射及两逆证明。

因此，有限交集关系列表确实控制全部维数上的相容条件。边界和 open box 的选面判据可判定，所以枚举由代码生成；任意不可判定的选面谓词则仍需显式提供完整枚举。

## 同步代表与同步关系是两步

给有限呈示到序列余极限的映射，先为有限个节点取得阶段表示。它们的关系在余极限中成立，但在最初表示的阶段未必成立。必须再为有限条关系取得共同后阶段见证，并取所有阶段的上界。

随后，阶段过渡的自然性保证每条重索引关系仍成立。预层的泛性质把这份有限证书扩展成全维自然变换。

`PresentationStages.factorThroughStage` 完成这一步。`WholeBoxStages.factorWhole` 用已证明的呈示比较，将它搬回实际 Boundary/OpenBox。

等式也有对应的同步定理：两个阶段映射在余极限中相等时，只需同步有限个生成节点上的等式，便能在一个更晚阶段得到整个自然变换的等式。`PresentationEqualities.equalAtLater` 实现这一步，并显式覆盖零节点情形：即使空列表的上界为零，两个原阶段仍须纳入最后的最大值。

`PresentationComparison` 将阶段映射按“在共同后阶段相等”取商，实际构造其到余极限映射集合的比较等价。这一结论针对代码中的序列与商；一般 filtered category 的版本仍是另外的工作。

## 图如何记录粘接

对每个节点使用网格图 \(I_m^{\otimes d_i}\)，按关系粘接顶点。两商顶点相邻，必须有同一张节点网格内的边作为见证。

二维三边 horn 是一个有用的检查：它包含正方形的全部四个顶点，却只有三条边。若把它改成正方形上这些顶点的诱导子图，就会补入缺失边。记有限节点粘接所得图为 \(G_m(P)\)。`GraphPresentation` 和 `SelectedGraphPresentation` 保留由各面生成的边，证明

\[
\operatorname{Gra}(G_m(P),G)
\cong\operatorname{Nat}(P,N_mG).
\]

`StagedFaceGraphs.graphRepresentation` 将整个 horn 映射转换为一个阶段 horn 图上的实际图映射，并附上恢复原映射的等式。

对于任意立方预层 \(A\)，`GraphCoend` 还构造所有 \((n,a,x)\) 的商顶点，关系来自预层重索引与网格作用。边仍由同一网格生成。其 Hom 双射、函子律、实际评价 counit 和两条三角等式均已写出；`GraphCoendAdjunction` 将它包装为库中的 \(\Gamma_m\dashv N_m\) 伴随。

`GraphPresentationComparison` 将有限节点图 \(G_m(P)\) 与全余端图 \(\Gamma_m P\) 连接成两个实际保边映射，并沿商生成元证明两逆；该模块已通过整库安全检查通过。这一比较不声称伴随 unit 或 counit 是弱等价。

## 与 Kan 性及 DHH 的距离

以上完成了 CK Kan 证明的阶段因子化和图解释部分。`UniversalHornReduction` 进一步固定

\[
H_{n,i,\varepsilon,k}=\Gamma_{k+1}(\sqcap^{n+1}_{i,\varepsilon}),
\qquad
u:\sqcap^{n+1}_{i,\varepsilon}\longrightarrow N_{k+1}H\longrightarrow N_\infty H.
\]

已通过整库安全检查的归约定理表明：若每个 \((n,i,\varepsilon,k)\) 的这个固定 \(u\) 都有截断填充，则任意 universe 的任意图 \(G\) 都有 `IsKan (N∞ G)`。证明先用整个 horn 的阶段因子化，再将通用填充沿余端泛性质给出的实际 \(H\to G\) 后合成；整体边界由自然性精确恢复。通用填充族位于 `Type₀`，两次截断消去都进入截断存在目标，不使用可数选择。

`HornFilling.universalFill` 现已给出每个通用单位 horn 的实际填充，`universalHornFillings` 是上述族的证明项。`HornRetraction` 构造扩大网格到实际生成 horn 图的保边映射，`HornBoundary.full-boundary` 恢复整个 horn 的自然变换；`StagePadding.middle-later` 和 `middle-include` 识别原交替阶段过渡。给定阶段 k 的完整 horn 时，`StageFilling.stageFill` 在 `tripleStage k = k + (suc k + suc k) = 3k + 2` 层使用边长 `3(suc k)` 的网格填充。

由此已经获得无条件的 `HornFilling.N∞-Kan : {ℓ : Level} (G : Graph ℓ) → IsKan (N∞ G)`，覆盖任意 universe、无限图、任意缺面位置及全部维数；`GeometricComparison.stableKan` 是其在既定几何比较接口上的实例。任意稳定 horn 的阶段存在仍保留命题截断，未提供 `ChosenKanFillings` 或规范阶段搜索。`N₁→N∞` 的 anodyne/弱等价仍须独立证明。

原论文强 DHH 进一步涉及完整立方富集的相干 nerve、原 A 群标记、marked Ex 局部化及空间模型的识别。有限呈示与伴随提供这些后续构造的基础，不构成 DHH 的证明，也不使旧候选类型自动成为原论文版本。

出处：[Carranza–Kapulkin，§3–4](https://arxiv.org/html/2202.03516v3)；原强猜想见 [Carranza–Kapulkin–Lindsey，Conjecture 14.3](https://arxiv.org/pdf/2306.02218v1)。历史回执为 **176 个模块，退出码 0，2026-10-12 13:55:35 UTC**；本次整库安全检查已通过 **190 个模块，退出码 0**，最新回执及源码 SHA-256 以 `checks/verification.json` 为准。`DayMonoidal`、`DayMonoidalLift` 因转换检查超时保留为未验收的历史草稿，未包含在本次迁移交付中，不计入正式源码验收。
