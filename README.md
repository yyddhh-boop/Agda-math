# Agda-math

数学学习与研究的 Agda 形式化代码。

## DHH 形式化

[源码与导读](formalization/dhh-agda/README.zh.md)包含自反无向图、BOX 乘积、全维立方 nerve、几何实现及 DHH 陈述所需的基础设施，允许无限图。

2026-10-13 的验收版本含 **206 个正式模块**，全部通过 Agda `--cubical --safe` 检查。新完成的 `HornFilling.N∞-Kan` 证明任意 universe、任意图、所有维数下的稳定 nerve 的普通 Kan 性。`N₁→N∞` 的弱等价和原 DHH 的模型比较仍未完成；本仓库不把这些基础设施称作 DHH 猜想的证明。

运行环境为 Agda 2.8.0；Cubical 0.9 的固定依赖源码及许可证已保存在 `vendor/cubical`。复现：

```sh
cd formalization/dhh-agda
python3 -u check.py
```

[验收记录](formalization/dhh-agda/checks/verification.json)保存实际编译版本、退出码、耗时和逐文件 SHA-256。[当前状态](formalization/dhh-agda/docs/original-paper-alignment.zh.md)区分已经构造的证明项与剩余接口。

首批新增11个基础模块，授权同步后又新增5个已验收模块：内部Hom构造和求值公式、原稳定合并操作的左右单位律及分步基础。未验收相容律草稿移出正式源码，并单独保存在 research-drafts/unverified，不计入验证。详见 [本轮范围](formalization/dhh-agda/docs/stable-enrichment-and-transition-progress.zh.md)。

尚未验收的研究源码单独保存在 [研究草稿](formalization/dhh-agda/research-drafts/unverified/README.md)，不计入206个正式验证模块。
