# 几何实现与局部化：本次形式化的基础边界

本次新增的 `DHH.Topology.Base` 真正定义了点集拓扑空间、连续映射、最终拓扑与集合商的商拓扑，并证明商的连续因子存在性及唯一性。`DHH.Topology.Category` 将它们组织成带 hom-set 的普通范畴。它们通过 `--safe --cubical` 类型检查，没有新增公理。

## 三种不同的“区间”

1. `Bool` 与 `Vertex (Q n)` 是有限离散组合数据。
2. Cubical Agda 的 `I : IUniv` 是语言内建的维度参数；它不是普通 `Type` 中的实数区间。重复的 `(i : I) → A` 可以表达参数化立方体，但不能把它替换成 `Vec I n : Type`。
3. 原始几何实现使用带通常拓扑的实数闭区间 `[0,1]`，其 n 次笛卡尔积为几何 n 立方体。

第三项必须被实际构造，或被明确保留为参数。仅有一个任意的协变 `DiskDiagram`，即使零维 disk 是单点，也不能保证它给出原始 DHH 的空间。CK 的定义恰好要求 `[0,1]^n`，并将 face、degeneracy、connection 分别解释为插入端点、删除坐标与相邻坐标的 max/min。[CK，Definition 2.2](https://arxiv.org/html/2202.03516v3#S2)

## 保留的工程测试模型（不用于 Concrete.DHH）

`DHH.Realization.DiscreteCubes` 为每一维取有限顶点集的离散拓扑，并实际构造了 `DiscreteCubeDiagram` 与 `DiscreteCubeGeometry`。

这个模型用来验证 coend 基础设施确实能被实例化。它不具备标准几何：其一维 disk 是离散两点，从这两点到任何空间的任意函数都是连续映射；把这样的映射称作“路径”，会把任意两个点连起来。因此它不能用于宣称原始弱同伦等价或原始 DHH 已经被固定。

## 标准实模型现已实际构造

- `Geometry/DedekindReals` 给出 located Dedekind cuts 的具体实数及 `[0,1]`，载体在 Type₁；`RealTopology` 用有理开区间基构造通常拓扑，证明 min/max 连续。
- `Topology/Basis`、`BasisConstructions`、`FinitePowers`、`IndexedProduct` 构造小基、乘积及子空间，不靠 powerset 的不合法小索引。
- `RealCubes` 构造真实区间的全部有限次乘积与生成词连续作用；`RealCubeDescent` 证明 Boolean 语义相同的生成词给相同真实连续映射。
- `RealCubeDiagram` 提供 `standardCubeGeometry`；`RealCubeChecks` 证明一维与 `[0,1]` 的实际同胚、端点计算及端点不同。
- `RealSimplex` 使用 endpoint-preserving monotone `Cut n→[0,1]`，给实际单纯形、所有序数算子和正确顶点作用。`CutClassification` 证明 cuts 与 n+2 元有限链的有序对应。
- `BasisLift`、`RealCubeLift`、`RealSimplexLift` 将同一实际几何提升到映射空间所需 Type₂；不用 resizing，也不随意另选一个 disk 模型。
- `Statements/Concrete` 固定以上实例，给闭合的 `DHH : Type₃`。

本项目拓扑公理允许载体 universe 内的小索引任意并。基拓扑处理了实际实几何所需的产品和升层；没有因此声称任意高 universe 开集都能降层。

## 仍需的模型证明

这些真实几何构造关闭了“几何只是参数”的旧缺口。与经典 π 群代数结构、经典 DK 局部化以及原文稳定 Kan nerve/富集图源的比较仍未形式化。Δ 呈示完整性已通过规范形及互逆函子证明，不再列为缺口。

## 为什么不把 TypeQuotient 直接称作几何实现

库中 `Cubical.HITs.Colimit.Base` 的注释与构造明确针对 graph-shaped homotopy colimit，只有对象点与箭头路径。普通 `TypeQuotient` 也只生成点和路径；这不自动包含范畴的复合单纯形及所有更高相容性。

即使另加复合三角形，也仍不能省略所有三维与更高构造。例如有序范畴 `[3]` 的 nerve 是三单纯形；只保留非退化二骨架会留下三单纯形的球面边界。这不是完整 classifying space。

采用集合商加商拓扑能避开这个问题：集合等式只处理点的识别，所有维数的几何信息保存在各 disk 的拓扑与商拓扑中，而非期待集合载体本身具有高阶 Agda 路径。

## DK 局部化的文献对照

Dwyer–Kan 的原始定义先对范畴取 free simplicial resolution，再逐维局部化；仅先取普通范畴的局部化、再取 nerve，会失去需要的派生映射信息。原文 §2.4–2.5 的 free functor 使用非恒等箭头作生成元，§4.1 定义 `L(C,W) = F_*C[(F_*W)⁻¹]`。若代码让恒等箭头也成为自由生成元，这是另一 free resolution；§4.5 给出比较这类版本所需的条件，比较定理本身仍需形式化。[Dwyer–Kan 1980，原文](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-1.pdf)

非恒等箭头被函子送到恒等箭头并不构成原构造的函子性反例：原自由函子将该生成元送到空词。当前无公理内部实现若直接取“非恒等箭头子类型”，需要审查是否在暗中判定恒等相等；一种待研究的安全路线是对全箭头词加入 `[id]=empty` 的 pointed-free 商。它与原文的识别及 DK §4.5 的增广弱比较都还没有证明。这个建议不是已构造的比较定理。

稳定 nerve 与论文整数模型的最新实际比较、几何富集和准范畴泛性质见 [原论文对齐记录](original-paper-alignment.zh.md)。该比较关闭稳定预层这一接口，不关闭本节其他模型义务。

此外，该文的 `O-Cat` 固定一个集合 `O` 作为对象集合。Cubical 库的 `Category` 允许对象类型具有非平凡相等路径，而 `Graph ℓ`、`Top ℓ` 一般没有 `isSet` 证明。引用经典局部化模型定理时，还需审查内部范畴与经典集合对象模型之间的编码或比较；代码构造通过类型检查不等于这项模型比较已经完成。
