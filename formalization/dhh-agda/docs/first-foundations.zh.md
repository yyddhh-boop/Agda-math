# DHH 文献的 Cubical Agda 形式化：第一批基础

你的想法适合这个问题。Cubical Agda 可以直接写出路径、路径之间的方块，以及更高阶的相容性，并检查附着边界是否真的匹配。它尤其适合把“图的组合数据怎样产生高阶同伦”写成精确的构造和证明。

这个项目从 Malle 的图映射与有限步同伦、BBdLL 的单位立方体神经入手。**它是历史文献形式化的第一批基础，尚未完成这些论文的全部定理，也没有证明 DHH。** 每个后续目标要有独立的类型、证明和原文定位。

## 两种立方体必须分开

图侧用的是有限图：

\[
I_m=\{0,\ldots,m\},\qquad Q_n=I_1\mathbin{\mathrm{BOX}}\cdots\mathbin{\mathrm{BOX}}I_1,
\qquad (N_1G)_n=\operatorname{Gra}(Q_n,G).
\]

BOX 中一次只能改变一个坐标。图映射允许把一条边压成顶点。顶点是集合，邻接是命题；这些定义允许无限顶点图，并没有把所有图限制成有限图。

类型论侧用 Agda 内建的 `I`、`PathP`、`Square` 和高阶归纳类型。`I` 不是具有两个顶点的图 \(I_1\)，也不是某个有限 \(I_m\)。图顶点之间的邻接 `Adj G x y` 更不能直接定义为顶点集合中的相等 `x ≡ y`；否则会把“相邻但不同”抹掉。[Agda 官方 Cubical 文档](https://agda.readthedocs.io/en/latest/language/cubical.html)

两层之间应当建立这样的桥：图的顶点成为实现中的点；图的边产生点之间的路径；合法方块产生路径之间的路径；更高的组合立方体给出更高的变形。这些构造的相容性要逐项证明。

已有两个形式化的边界检查：

- `diagonal-not-hom`：函数 \(b\mapsto(b,b)\) 不能成为 \(I_1\to I_1\mathrm{BOX}I_1\) 的图映射。它把一条边送到了同时改变两个坐标的对角线上。
- `no-square-with-these-corners`：在图 \(0-1-2\) 中，方块角点 \(00=0,10=1,01=2,11=2\) 的底、右、顶三边合法，左边需要 \(0\sim2\)，因此无法扩张成合法方块。它允许角点只是路径相等，不依赖某种特定的边证明。

这批代码还没有定义一般 horn 对象。上述定理证明的是具体的扩张障碍。Agda 的 `hcomp` 填的是已经处在某个类型中的开放盒；它不会给原图补一条不存在的邻接边。CK 的 Kan 性质属于细分后的 \(N_\infty G\)，需要单独的数学证明。[CK 原文导言与 §3](https://arxiv.org/html/2202.03516v3)

## 项目中的定义与证明

| 模块 | 内容及准确范围 |
|---|---|
| `DHH.Graph` | 自反无向图、保持邻接的映射、BOX、映射外延性、恒等与复合规律。邻接证明没有额外的多重性。 |
| `DHH.FiniteInterval` | 两顶点单位区间；四顶点线性区间 \(I_3\)，用于图解中的具体路径。 |
| `DHH.FinitePath` | 对任意自然数 \(m\) 构造 `PathGraph m`，顶点 `Fin (m+1)`，相邻整数间有边。证明有限顶点字符串与相应图路径的双向构造，提供区间嵌入与平移。 |
| `DHH.Cubes` | 任意维 \(Q_n\)、全部组合立方体映射、任意坐标 faces/degeneracies/min/max connections。证明不同坐标的 face、degeneracy 交换及两类混合公式，同坐标 face-degeneracy 公式、connection 的指定单位面公式；证明后复合的恒等、复合与全部操作的自然性。完整的 connection identities 尚未全部证明。 |
| `DHH.Homotopy` | 一步变形 `Step`、保留实际有限序列的 `Chain`、存在有限链的命题 `Homotopic`；自反、对称、传递、前后复合相容；一步变形与 BOX 柱体的双向构造和柱体往返。尚未定义 string fundamental group 或全部 \(A_n\)。 |
| `DHH.Cellular2` | 一个明确命名的辅助高阶归纳类型 `Cell₂ G`：点、边、所有合法方块；方块使两条边界路线相等；带完整方块数据的解释函数及其点、边、方块计算规则。 |
| `DHH.CubicalBridge` | `Cube G 2` 与四点四边描述 `GraphSquare G` 的同构，两次往返均有证明；因此每个组合方块在 `Cell₂ G` 中提供一条二阶路径。 |
| `DHH.BoundaryChecks` | 对角线不是 BOX 边、指定三边不能补成方块的不存在定理。 |
| `DHH.Examples` | 四边环 \(C_4\) 的具体图映射、有限步收缩；带停留步的两条路径及端点固定的网格变形；错误的一步短路径变形的否证。 |
| `DHH.HomotopyCategory` | 图映射按有限链同伦的集合商、复合良定义、单位与结合律，构成普通范畴 `HoGraph`；实际图同伦等价给出该范畴中的同构。 |
| `DHH.NerveExamples` | 将四边环方块及三边扩张障碍接到精确的单位方块映射定义；构造四边环与点的实际图同伦等价及 `HoGraph` 中的同构。 |

注意：`Cell₂ G` 是一个**自由的二维生成元展示**。这批代码没有识别全部退化方块，也没有加入神经中的所有高阶胞腔。因此既没有证明 `Cell₂ G ≃ |N₁G|`，也不能用它计算全 \(NG\) 的高阶同伦群。它的意义是先形式化“边界相容的方块会给出路径同伦”这一机制。高阶归纳类型中的二维生成元并不意味着这个类型是 2-type。

`HomotopyCategory` 已纳入总检查入口，表示按有限链同伦取商的**普通范畴**。其态射集合只保存映射的同伦类；它不是 DHH 要求的完整映射空间，也不是图在全弱等价下的 \(\infty\)-局部化。

## 从四边环读懂代码

用 \(a,b,c,d\) 标记循环。短路径

\[
(a,b,c),\qquad(a,d,c)
\]

中间顶点 \(b,d\) 不相邻，所以同一参数长度下不能直接用一个时间步变过去。增加停留步后，合法网格是

\[
\begin{matrix}a&a&b&c\\a&d&c&c\end{matrix}.
\]

每一行保持空间方向邻接，每一列保持时间方向邻接，左右端点始终是 \(a,c\)。这是一个 \(I_3\mathrm{BOX}I_1\to C_4\) 的图映射，不是用 Agda 的 Kan 操作补出的图边。

中间的单位方块对应角点 \(a,b,d,c\)。在 `Cell₂ C₄` 中，`routesAgree` 的类型表达

\[
(a\to b)\cdot(b\to c)=(a\to d)\cdot(d\to c).
\]

等号左、右两边都是路径，所以这一条等式自身是二维同伦。它直接展示了为什么从一维关系出发，会有需要更高维语言表达的数据。

先读 `DHH.Examples` 的具体标签，再读 `DHH.Cellular2` 的 `tile` 与 `routesAgree`，最后看 `DHH.CubicalBridge` 的两个往返证明。这样可以把计算、组合定义和高阶路径分别看清楚。

## 文献到形式化的顺序

| 文献与原文位置 | 本轮对应 | 后续证明义务 |
|---|---|---|
| [Malle 1983，第 4–10 页](https://web.math.pmf.unizg.hr/glasnik/18.1/18101.pdf) | 图映射、有限步 net homotopy 的基础性质及具体收缩。采用自反图来表达允许停留与压边，须与原文无环约定明确对照。 | string、停留步、端点固定同伦的商、基本群及运算良定义。 |
| [Babson–Barcelo–de Longueville–Laubenbacher，2004 预印本 §2–4](https://arxiv.org/pdf/math/0403146) | \(Q_n\) 映射、faces、degeneracies；另加入现代 connection 操作的图映射合法性。 | 先形式化原文按 faces/degeneracies 定义的实现及其普遍性质。若选现代带 connections 的立方范畴，另定义其实现并证明两个版本的比较。 |
| [同文 Theorem 5.1 / Property 6.1](https://arxiv.org/pdf/math/0403146#page=6) | 尚未形式化该条件性比较定理。 | 网格 \(A_n\)、群结构、比较同态与立方逼近义务；不能把旧文条件当成已证公理。 |
| [Carranza–Kapulkin，2022/2024，§3–5，固定 v3](https://arxiv.org/html/2202.03516v3) | 本轮提供其图与 \(N_1\) 基础输入。 | \(N_m\)、transition maps、\(N_\infty\)、Kan 定理、\(N_1\to N_\infty\) 比较、\(A_n\cong\pi_n\)。使用 anodyne 证明前要核对项目文献审查所记录的后续修正。 |
| [Carranza–Kapulkin–Lindsey，2023 v1，Conjecture 14.3](https://arxiv.org/pdf/2306.02218v1#page=62) | 尚未形式化强猜想。必须固定 v1；后来的版本删除了应用章节。 | 图的高阶局部化、空间范畴、对象实现与完整 mapping-space 比较。 |
| [Carranza–Kapulkin，2026，Theorem 4.5](https://arxiv.org/html/2602.19293v1) | 尚未形式化有限阶 DHH 定理。 | cubification、图 realization、有限 \(n\) 的比较与局部化。固定 \(n\) 的结论不能作为完整 DHH 的公理。 |

Atkin 和早期单形连通性工作的历史动机可保存在阅读笔记中；未经原文核对的具体定理不先写成形式化目标。其他读取规则，如 clique complex 和 Hom complex，需要各自的模块，不能用它们的普遍性替换这里的 \(N_1\)。

接下来应先完成完整的 cubical identities，尤其 connections 的混合公式；再把网格同伦与实现空间中的路径同伦连起来。若这些接口能统一表达，才适合推进 CK 的全维比较。直接先做强 DHH，会把尚未建立的结构埋在大量假设中。

## 复现与依赖

本机编译器：`Agda version 2.8.0-3d04bac`。依赖为 Cubical 0.9，源代码固定于 commit `b150186d2544e7efeddd31e5d14a8b9ecbb100f7`，已经复制到本项目 `vendor/cubical`，并保留许可证。没有修改原来的 Cubical 安装或任何同步的项目参考文件。官方兼容表列出 Agda 2.8.0 与 Cubical 0.9 的对应关系。[Cubical 官方兼容表](https://github.com/agda/cubical#compiling-using-and-installing)

在这个项目目录运行：

```sh
python3 check.py
```

如果 Agda 不在 PATH，检查脚本会尝试本机的 `~/.local/bin/agda`；也可以给出明确路径：

```sh
python3 check.py --agda /absolute/path/to/agda
```

检查入口是 `Everything.agda`。每个本项目模块都启用 `--cubical --safe`。检查脚本还审查项目源码中的未证明公理、洞及绕过检查的选项，并把编译器版本、依赖版本、退出码及源码 SHA-256 记入 `checks/verification.json`，编译输出保存在 `checks/latest.log`。

2026-10-11，12 个项目模块的总入口实际检查成功，退出码 0。独立语义审查核对了 BOX、立方体公式、二维桥、普通同伦范畴和四边环例子，并据此修正了原文范围说明。

依赖库会产生 `UnsupportedIndexedMatch` 警告；检查命令沿用 Cubical 库的 `-WnoUnsupportedIndexedMatch` 设置。这涉及部分索引归纳类型的函数在 transport 上的计算限制，不是允许未证明目标或关闭安全检查。本项目不声称这些函数具有完整的 transport 定义性计算。[Agda 官方说明](https://agda.readthedocs.io/en/latest/language/cubical.html#indexed-inductive-types)

这个保证相对于 Agda 编译器、Cubical 类型论的内建规则及固定的标准库依赖。没有给本文献目标添加 `postulate`，也没有以未完成的证明洞代替定理。标准库已有的声明仍属于依赖基础；源码审查的“无 postulate”范围是本项目自己的模块。
