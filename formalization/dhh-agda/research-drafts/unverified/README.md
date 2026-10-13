# 未验收的研究草稿

这里保存本轮已写出但尚未通过完整检查的11个相容律草稿，使用`.agda.txt`以避免误计入正式Agda入口。正式验收仍是`../../Everything.agda`覆盖的201模块，见`../../checks/verification.json`。

这些文件不能作为已证明结论：稳定富集的完整单位与结合律、nerve作用保持式，以及Day内部Hom复合包装仍待验证。转换检查超时不是通过；具体诊断见`../../checks/comparison-development-diagnostics.json`。没有提供完整DHH、原始N₁→N∞弱等价或完整局部化模型的证明。

后续恢复时把需要检查的模块复制到工作目录，逐模块检查所有依赖后再纳入正式DHH树。不要仅把扩展名改为`.agda`就宣称完成。
