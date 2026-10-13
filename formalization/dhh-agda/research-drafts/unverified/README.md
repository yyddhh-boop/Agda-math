# 未验收的研究草稿

最新正式入口覆盖217个模块，全部通过安全检查，逐文件哈希见 `../../checks/verification.json`。本目录保留前一轮12份历史未验收源码，并新增 `continuation-20261013/` 中的16份候选和替代稿，均使用 `.agda.txt` 扩展名，不计入正式模块。

本轮已移入正式树的11个模块见 `../../checks/enrichment-continuation-index.json`。稳定cell结合律、Day完整参数求值及Hom外延性已验收；完整Day单位/结合图、最终curry桥、富集实例和nerve函子保持式尚未验收。超时不是通过，也不是数学反例。

历史Parameter草稿与最新正式分层实现不同；历史DayUnits也依赖尚未验收的扩展Core。继续研究时需在树外复制所选候选及准确依赖，检查成功后再移入正式入口。所有模型边界见 `../../docs/enrichment-continuation.zh.md`。
