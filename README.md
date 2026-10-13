# Agda-math

数学学习与研究的 Agda 形式化代码。

## DHH 形式化

[源码与导读](formalization/dhh-agda/README.zh.md)包含自反无向图、BOX乘积、全部维数的立方 nerve、真实几何实现及 DHH 陈述所需基础，允许无限图。

最新验收版本含 **217 个正式模块**，全部通过 Agda `--cubical --safe --guardedness` 检查。相比206模块版本新增11模块，关闭任意稳定cell结合律、完整Day参数求值图、内部Hom外延性及坐标相容；详见 [本轮续接](formalization/dhh-agda/docs/enrichment-continuation.zh.md)。完整富集图式、同伦相干nerve、原文标记局部化及固定比较仍未闭合。目标是完整陈述原文Conjecture14.3；不要求证明猜想自身。

Agda2.8.0与Cubical0.9固定依赖已保存在vendor/cubical并附许可证。复现：

```sh
cd formalization/dhh-agda
python3 -u check.py
```

[验收回执](formalization/dhh-agda/checks/verification.json)保存编译器、真实退出码、时间、耗时与全部正式源码SHA-256。[原文状态](formalization/dhh-agda/docs/original-paper-alignment.zh.md)保留模型和剩余接口边界。

[研究草稿](formalization/dhh-agda/research-drafts/unverified/README.md)保留12份历史草稿与16份本轮候选，均为树外 `.agda.txt`，不计入217个正式模块。转换超时没有被算作证明通过。
