> 本文记录树外未验收相容律草稿的精确接口与开发审查；不计入最新正式217模块验收（本文草稿范围为历史记录）。当前正式结果见 `stable-enrichment-and-transition-progress.zh.md`，编译回执见 `checks/verification.json`。

# 稳定图富集与 nerve Hom 作用的相干性接口

这份记录说明本轮新增源码的数学接口和模块拆分。各模块的最终通过状态由根代理完成的检查日志统一确认；有完整证明项、通过某个截取前缀或运行超时，都不能代替完整模块检查成功。

## 实际比较的映射

固定任意 universe `ℓ`，令

\[
M(G,H)=N_\infty\operatorname{HomGraph}(G,H),\qquad U=\operatorname{DayUnitAt}(\ell).
\]

`stableComposition` 是原有 `StableComposition.agda` 中已经构造的真实 Day 复合

\[
m_{G,H,K}:M(H,K)\otimes M(G,H)\longrightarrow M(G,K).
\]

新增源码给出实际单位 `stableIdentity : U → M(G,G)`，并准备检查以下两个单位图及结合图：

\[
m_{G,H,H}(\eta_H\otimes 1)=\lambda_{M(G,H)},\qquad
m_{G,G,H}(1\otimes\eta_G)=\rho_{M(G,H)},
\]

\[
m_{G,H,L}(m_{H,K,L}\otimes 1)
=m_{G,K,L}(1\otimes m_{G,H,K})\alpha.
\]

这里的 `λ`、`ρ`、`α` 分别是实际 `dayLeftUnitAt`、`dayRightUnitAt`、`dayAssociator`。两个结合路线的共同定义域为 `((M(K,L) ⊗ M(H,K)) ⊗ M(G,H))`。`⋆n` 按源码约定从左到右执行。

## 模块和缓存边界

| 模块 | 负责的完整接口或证明项 |
|---|---|
| `GridCompositionCoherence` | 任意有限网格大小、全部维数的 split/append 外延性，真实 cube 单位与结合子的有限网格作用，以及有限阶段复合的单位和结合律。四个图可以处在不同 universe。 |
| `StableCompositionStageLaws` | 原有 `mergeN∞-same-stage` 的精确 typed abstract 封装。声明直接复用原证明，保持同一稳定复合及同一公式。 |
| `StableCompositionIdentity` | 透明构造 `stableIdentity`，显式消去交替过渡的 Bool 分支，证明常值单位可出现在任意阶段。 |
| `StableCompositionMergeUnits` | 左右阶段单位证明的完整 `e1/e2/e3` 中间路径，以及通过稳定 cell 商消去得到的 `mergeN∞` 左右单位律。 |
| `StableCompositionDayUnits` | 利用真实 Day 配对生成元外延性，得到稳定复合与实际左右单位子的自然变换等式。 |
| `StableCompositionUnits` | 公开重导出前三个单位模块，保留原单位接口；本模块没有补加假设。 |
| `StableCompositionAssociativity` | 三个稳定输入提升到共同阶段，有限阶段结合律降商，再通过三块 Day 生成元外延性得到真实 Day 结合图。 |
| `StableCompositionCoherence` | 公开重导出单位和结合模块，保留原统一入口。 |
| `NerveFunctorUnit` | 实际稳定求值的单位图，及原有 `nerveHomMap` 到几何 internal Hom 的保恒等等式。通用 curry 参数相容性保留四个独立 universe。 |
| `NerveFunctorComposition` | 实际稳定求值的逐阶段计算公式与完整 Day 结合图。 |
| `NerveFunctorCoherence` | 通过精确的三段 curry 等式，将求值结合图转为原有 `nerveHomMap` 对实际 `homComposition` 的保复合等式；单位目标为实际 `homIdentity`。 |

共享的 `DayClosedParameter` 提供实际闭伴随的求值 β、uncurry 单射性和参数预复合相容性，量化四个独立 universe。`DayHomComposition` 用真实 Day 求值及结合子构造 `homIdentity`、`homComposition`，并提供 curry 后的复合公式。

`DayHomComposition` 的内部缓存组件为 `DayHomEvaluation`、`DayHomNestedEvaluation`、`DayHomCompositionMaps`、`DayHomCompositionNaturality`；旧入口公开重导出原有名字，`NerveFunctorCoherence` 的导入接口保持一致。

拆分只改变完整模块的检查与缓存边界。原 `StableComposition` 的构造和证明没有修改。`stableIdentity`、`stableAction`、实际 Day 映射、网格作用与 nerve 构造保持透明；`abstract` 只用于等式证明，供下游使用其精确路径类型，避免重复展开大型商证明项。

## 阶段证明与商消去

阶段单位证明明确列出三段路径：先把常值稳定单位同步到输入所在阶段，再应用同阶段稳定复合公式，最后应用真实有限网格单位律。左右单位均保留与实际 cube 单位子的重索引公式。

结合律在商消去内部读取三个带阶段输入 `(k,a)`、`(l,b)`、`(m,c)`，取有限共同阶段

\[
s=\max(k,\max(l,m)),
\]

并使用现有 `point-advance` 与明确的 `k≤s`、`l≤s`、`m≤s` 证书。目标等式是命题，`SQ.elimProp3` 只进行合法的命题消去；没有选择全部稳定 cell 的规范代表，也没有假定图或 Hom 顶点可枚举。

稳定层沿用原 `StableComposition` 的固定图 universe `ℓ`，并量化任意 `ℓ`、任意图及所有自然数维数。整个构造允许无限图。

## nerve Hom 作用的确切目标

`nerveHomMap` 的目标为原有几何 `DayHom (N∞ G) (N∞ H)`。新的保复合证明链依次使用：

1. 真实 curry 参数预复合公式；
2. 已准备检查的实际稳定求值结合图；
3. 实际 internal-Hom 复合 `homComposition` 的 curry 公式的反向等式。

于是待检查的最终接口为

\[
\varphi_{G,K}m_{G,H,K}
=c_{N_\infty G,N_\infty H,N_\infty K}
(\varphi_{H,K}\otimes\varphi_{G,H}).
\]

右侧 `c` 是 `DayHomComposition.homComposition` 的实际构造。这里只把已构造的同一求值路线通过闭伴随转换，没有重新命名右侧使结论自动成立。

## 验证和剩余义务

所有新增 Agda 源均声明 `--cubical --safe`，没有加入 hole、postulate、有限性假设或选择公理。根代理串行检查共享依赖和缓存；本轮性能诊断使用过 `--syntactic-equality=64`，切换该参数会使相关依赖缓存重新检查，最终状态必须结合完整日志判断。

若本 checkpoint 的完整检查仍超时，对应完整 proof 源保留为待检查草稿，且不计入已通过模块。独立只读审查已经检查了单位、结合子、共同阶段路径、abstract 边界及最后 curry 链的方向，未发现具体来源或目标不匹配；这同样不替代 Agda 检查。

本轮这些相干性接口不包含 `N₁→N∞` 的原始弱等价、几何 `DayHom` 的 Kan 性、严格对象集合构造、原 DHH 的局部化或模型比较。它们应分别继续作为明确义务；局部稳定 Hom nerve 的 Kan 性由本轮另一个独立模块提供，不能据此消去几何 Hom 弱比较的义务。
