# 未验收的研究草稿

当前正式入口 `../../Everything.agda` 覆盖206个模块，全部通过安全检查，逐文件哈希见 `../../checks/verification.json`。此目录单独保存12份未验收研究源码，扩展名为 `.agda.txt`；其中10份当前候选和2份替代实现，不计入正式模块。

已通过的内部Hom构造与求值β、原稳定合并操作左右单位律已移入正式树。这里仍保留完整Day单位自然变换等式、稳定结合律、nerve函子保持式及参数相容律等未验收尝试。转换超时不是通过，诊断见 `../../checks/comparison-development-diagnostics.json`。

`StableCompositionMergeCore-DayMapAttempt.agda.txt` 是在正式Core之上扩展Day复合包装的未验收尝试，当前DayUnits草稿需要这些扩展。`DayHomCompositionNaturality-ParameterAttempt.agda.txt` 是采用参数包装的替代证明，需要同目录的Parameter草稿。它们不能替换正式模块并声称已经证明。

继续时将候选和所需依赖复制到工作目录，实际检查成功后才能纳入正式入口。当前内容不提供原始N₁→N∞弱等价、完整模型识别或DHH证明。
