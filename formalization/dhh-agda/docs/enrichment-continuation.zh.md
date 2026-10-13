# 原文陈述目标：稳定结合律与 Day 参数求值续接

本轮目标是完整构造 Carranza–Kapulkin–Lindsey 原文 Conjecture 14.3 的源、目标和固定比较箭头，再把它是准范畴等价写为待证类型；不要求证明猜想自身。

本轮正式模块与改变列表见 `../checks/enrichment-continuation-index.json`。最新217模块整库安全检查退出码0，2026-10-13 20:43:18（北京时间），耗时147.765秒。最终整库验收以 `../checks/verification.json` 的实际退出码和全部源码哈希为准；前一版206模块回执保存在 `../checks/verification-before-enrichment-associativity.json`。

## 新关闭的数学义务

1. `StableCompositionMergeAssociativityStages`：两个嵌套的原稳定合并操作分别同步到同一个有限阶段，以实际网格结合式和 includeStage 自然性比较。重索引是确切的 `cubeAssociator p q r`。
2. `StableCompositionMergeAssociativity`：对三个集合商作命题消去，输入分别提升到 `max k (max l m)`。由此取得任意三个稳定 cell 的结合律；没有选择代表，没有有限图或有限维假设。
3. `DayHomCompositionPrecompose`：任意参数预复合与实际内部 Hom 组合的 curry 构造相容。
4. `DayHomCompositionParameterCore`、`ParameterEvaluationCore`、`ParameterPairing`、`Parameter`、`ParameterRoute`：实际参数映射及其求值、完整配对计算式、三块参数求值公式，并通过三重 coend 外延性证明整个参数求值自然变换等于真实 nestedEvaluation。
5. `DayHomGeneratorExt`：内部 Hom 求值对两块坐标重索引相容；任意一个 Hom cell 的全部恒等 chart 求值决定这个完整自然变换，不限于0-cell。
6. `DayHomUnitCharts`：实际立方结合子与左、右单位子的两条全维坐标等式。
7. `CubicalCategory`：精确记录任意对象类型上的 Day 富集数据及完整单位/结合图，并定义 LocallyKan。它只给出结构记录；本轮未取得 stableGraphCategory 的完整实例。

稳定结合律比较 `mu(mu(a,b),c)` 与沿实际立方结合子重索引的 `mu(a,mu(b,c))`。每个图可无限，每个维数可任意；三个参数维数彼此独立。这里的 mu 是已有 mergeN∞ 的已检查 abstract 包装，并有逐应用识别等式。没有替换图的 BOX 产品或稳定 nerve。

## 检查器展开控制

`StableComposition` 的稳定合并、阶段/重索引规律、Day 复合及配对 beta 放入同一个 opaque 块；`DayTensorFunctor` 的实际 dayMap 及三条已证明规律也放入 opaque 块。原数学定义和证明体保留。依赖者使用已检查的计算公式，避免自动展开多层商消去。该机制由 [Agda 2.8 opaque 文档](https://agda.readthedocs.io/en/v2.8.0/language/opaque-definitions.html)说明。

只有这两个原正式模块修改了展开边界；其余原DHH源码保持。最终整库安全检查负责确认所有依赖仍能检查。

## 尚未关闭的结构接口

- 完整稳定 Day 左右单位图和结合图。
- 内部 Hom 完整单位/结合图及最终 curry 组合自然性；本轮有完整求值图，末端 curry 拼接仍有转换超时。
- 原 nerveHomMap 保持单位与复合的完整等式，以及目标 DayHom 的局部 Kan 性。
- 实际同伦相干 nerve N□、标记 Exop+ 及固定诱导 barN。
- 原文 A 群/W 标记的直接构造或与现有弱等价的识别。
- 全对象模型与经典集合值 nerve 的基础接口，以及所选择路线实际需要的空间模型比较。

原 N₁→N∞ 弱等价与旧 DK 分辨模型比较仍未形式化；走原文直接路线不必先完成所有旧候选桥接。稳定 cell 结合律和类型正确的结构记录不独自构成 N□Graph。

## 未验收尝试

本轮未验收替代稿保存在 `../research-drafts/unverified/continuation-20261013/`，扩展名为 `.agda.txt`，不纳入 Everything 或源码数量。它们包括实际 Day 单位图、完整 Hom 单位/结合图、完整富集实例以及未通过的 beta/curry 桥。

转换超时只表示未验收，不表示数学反例。本轮没有添加 postulate、证明洞、不安全检查选项，也没有提供 DHH 的证明项。
