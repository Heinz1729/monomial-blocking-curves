# 手稿的 Lean 陈述与证明

工程使用 Lean 4.8.0，mathlib 固定在 `b5eba595428809e96f3ed113bc7ba776c5f801ac`。最小值使用 `IsLeast`，同时表达参数集的存在性和对所有参数集的下界。[手稿](../Manuscript.pdf) · [构建入口与公理清单](BlockingCurves.lean) · [锁文件](lake-manifest.json)

## 从原问题到形式陈述

| 审阅问题 | 独立可查的接口 |
| --- | --- |
| 是否表达原文的阻塞问题？ | [ProblemStatement](ProblemStatement.lean) 只导入 mathlib，写下原文 (5.3)–(5.4) 的值集相交条件。[StatementComparison](StatementComparison.lean) 证明它等价于 [Projective](Projective.lean) 的齐次射影条件，换元为两个参数同时取负。[AGY 原文，§5](https://arxiv.org/html/2510.15332v2) |
| 曲线几何不可约吗？ | [GeometricIrreducibility](GeometricIrreducibility.lean) 在三个变量的多项式环中构造原式，核验总次数意义下的齐次性、求值为零的等价式、标量扩张到代数闭包后的不可约性。 |
| 何时是非平凡阻塞集？ | [NontrivialPencil](NontrivialPencil.lean) 证明对所有次数至少 2 的曲线并，不含整条有理直线当且仅当参数集为真子集。在 Frobenius 情形给出可达的非平凡最小值和全域退化判据。 |
| scattered 是否对应文献术语？ | [ScatteredComparison](ScatteredComparison.lean) 将非零向量的相同斜率条件与 [GeneralGeometry](GeneralGeometry.lean) 的核维数条件等同。[Zanella，§1](https://arxiv.org/abs/1909.07802) |
| 不同有限域模型的结论如何互用？ | [FieldTransport](FieldTransport.lean) 经域同构搬运任意参数集的阻塞谓词及最小值。[PrimeFieldInstances](PrimeFieldInstances.lean) 在与定理 1 相同的 `GaloisField` 接口上陈述 41、47 两个结论。 |

这些比较来自同一工程。数学文献给出陈述的外部来源，等价证明、复现脚本和 CI 的维护责任均在本仓库。这里没有第三方维护的形式基准或人类同行评审认证。

## 定理入口

| 手稿 | 从陈述追到证书 |
| --- | --- |
| 定理 1 与定理 3 | [Paper](Paper.lean) 的 `projective_prime_power_minimum` 经 [Frobenius](Frobenius.lean) 和 [MainResult](MainResult.lean) 化为仿射超平面阻塞数。[LowerBound](LowerBound.lean) 与 [UpperBound](UpperBound.lean) 证明上下界。[GeneralGeometry](GeneralGeometry.lean) 证明 scattered 的充要刻画。 |
| 八元域 | [F8Example](F8Example.lean) 核验位运算与 256 个掩码。[F8Semantics](F8Semantics.lean) 将这些掩码与八元域全部参数集双射，逐集保基数和阻塞性。`projective_optimal_count` 在 `GaloisField 2 3` 上计得 56 个四元最优集。 |
| 定理 2，模 41 | [位表](Cubic41.lean) → [逐线方程](Cubic41Semantics.lean) → [归一化](CubicSymmetry.lean) → [全局最小值](CubicGlobal.lean) 与 [328 个最优集](CubicOrbit.lean)。 |
| 定理 4，模 47 | [位表](Cubic47.lean) → [逐线方程](Cubic47Semantics.lean) → [归一化](Cubic47Symmetry.lean) → [全局最小值](Cubic47Global.lean) 与 [轨道及稳定子](Cubic47Orbit.lean)。两锚点枚举覆盖 990 个四元和 14,190 个五元候选。 |
| 第 7–10 节的三次避碰引理 | [CubicSlope](CubicSlope.lean) 核验有理临界值的方程及由差集条件选出无碰撞斜率。单值、迹估计和对数定理的证明见手稿。 |

## 复现与验证记录

在仓库根目录先进入 `lean/` 运行 `lake exe cache get`，然后回到根目录运行 `python checks/verify_lean.py`。脚本执行 `lake build`，重放入口的每条 `#print axioms`，检查所有源码模块均在入口导入闭包内，再以 Lean 自带的公理收集器递归追踪所有安全声明和带源码位置的不安全声明。编译器产生的无源码不安全辅助符号不单独用作根；从根出发的依赖闭包全量检查。允许的公理是 `Classical.choice`、`Quot.sound`、`propext`。

[verification.txt](verification.txt) 记录逐定理结果以及所有 Lean 源码、工具链和锁文件的 SHA-256。输入规范为 LF 换行，Linux 与 Windows 可以对照同一记录。修改源码后运行 `python checks/verify_lean.py --write`，审阅新的哈希与公理差异并与源码一同提交。[验证程序](../checks/verify_lean.py)
