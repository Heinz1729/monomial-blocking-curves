# 手稿的 Lean 陈述与证明

工程使用 Lean 4.8.0，mathlib 固定在 `b5eba595428809e96f3ed113bc7ba776c5f801ac`。最小值使用 `IsLeast`，同时表达参数集的存在性和对所有参数集的下界。[手稿](../Manuscript.pdf) · [构建入口与公理清单](BlockingCurves.lean) · [锁文件](lake-manifest.json)

## 从原问题到形式陈述

| 审阅问题 | 独立可查的接口 |
| --- | --- |
| 是否表达原文的阻塞问题？ | [ProblemStatement](ProblemStatement.lean) 只导入 mathlib，直接定义射影化的点与直线、关联关系、次数恰为 $d$ 的几何不可约齐次曲线、定义 1.1 的曲线族与问题 5.4 的最小值，并保留值集条件。[StatementComparison](StatementComparison.lean) 验证任意坐标代表的关联与曲线方程，`AGY_minimum_iff` 将原始最小值与 [Projective](Projective.lean) 的齐次坐标陈述等同。[AGY 原文](https://arxiv.org/html/2510.15332v2) |
| 曲线几何不可约吗？ | [GeometricIrreducibility](GeometricIrreducibility.lean) 在三个变量的多项式环中构造原式，核验总次数意义下的齐次性、求值为零的等价式、标量扩张到代数闭包后的不可约性。 |
| 何时是非平凡阻塞集？ | [NontrivialPencil](NontrivialPencil.lean) 证明对所有次数至少 2 的曲线并，不含整条有理直线当且仅当参数集为真子集。在 Frobenius 情形给出可达的非平凡最小值和全域退化判据。 |
| scattered 是否对应文献术语？ | [ScatteredComparison](ScatteredComparison.lean) 将非零向量的相同斜率条件与 [GeneralGeometry](GeneralGeometry.lean) 的核维数条件等同。[Zanella，§1](https://arxiv.org/abs/1909.07802) |
| 不同有限域模型的结论如何互用？ | [FieldTransport](FieldTransport.lean) 经域同构搬运任意参数集的阻塞谓词及最小值。[PrimeFieldInstances](PrimeFieldInstances.lean) 在与定理 1 相同的 `GaloisField` 接口上陈述 41、47 两个结论。 |

这些比较来自同一工程。数学文献给出陈述的外部来源，等价证明、复现脚本和 CI 的维护责任均在本仓库。外部审阅者可仅对照 `ProblemStatement.lean` 和原文检查问题的翻译。

## 定理入口

| 手稿 | 从陈述追到证书 |
| --- | --- |
| 定理 1 与定理 3 | [Paper](Paper.lean) 的 `projective_prime_power_minimum` 经 [Frobenius](Frobenius.lean) 和 [MainResult](MainResult.lean) 化为仿射超平面阻塞数。[LowerBound](LowerBound.lean) 与 [UpperBound](UpperBound.lean) 证明上下界。[GeneralGeometry](GeneralGeometry.lean) 证明 scattered 的充要刻画。 |
| 八元域 | [F8Example](F8Example.lean) 核验位运算与 256 个掩码。[F8Semantics](F8Semantics.lean) 将这些掩码与八元域全部参数集双射，逐集保基数和阻塞性。`projective_optimal_count` 在 `GaloisField 2 3` 上计得 56 个四元最优集。 |
| 三十二元域，六次 | [域运算与参数行](Sextic32.lean) 和[归一化六元集枚举](Sextic32Search.lean) 给出无解证书和一个七元见证。[位表语义](Sextic32Geometry.lean) 与[全局最小值](Sextic32Global.lean) 将证书搬运到 `GaloisField 2 5`。七元最优集总数和仿射轨道由[两种 Python 穷举](../checks/sextic32.py)逐集交叉核对。 |
| 定理 2，模 41 | [位表](Cubic41.lean) → [逐线方程](Cubic41Semantics.lean) → [归一化](CubicSymmetry.lean) → [全局最小值](CubicGlobal.lean) 与 [328 个最优集](CubicOrbit.lean)。 |
| 定理 4，模 47 | [位表](Cubic47.lean) → [逐线方程](Cubic47Semantics.lean) → [归一化](Cubic47Symmetry.lean) → [全局最小值](Cubic47Global.lean) 与 [轨道及稳定子](Cubic47Orbit.lean)。两锚点枚举覆盖 990 个四元和 14,190 个五元候选。 |
| 第 7–10 节的三次避碰引理 | [CubicSlope](CubicSlope.lean) 核验有理临界值的方程及由差集条件选出无碰撞斜率。单值、迹估计和对数定理的证明见手稿。 |

## 渐近证明的形式化范围

| 手稿步骤 | Lean 所证结论及其输入 |
| --- | --- |
| 第 11 节，同时无根 | [FrobeniusCoset](FrobeniusCoset.lean) 对任意有限二重传递作用，证明任意置换乘该群所得的陪集含错排。[CubicAsymptotics](CubicAsymptotics.lean) 的 `twist_point_threshold` 给出亏格与分歧纤维上界保证有理点余量为正的数值阈值。几何群包含单群直积、实际曲线的亏格界和扭曲下降见手稿。 |
| 第 12、16、18 节，三次下界 | [CubicPairCount](CubicPairCount.lean) 定义实际的无根有序对数和固定斜率截距数，证明阻塞迫使相应计数为零。给定式 (12.1) 或第 18 节固定斜率的迹误差，[CubicAsymptotics](CubicAsymptotics.lean) 与此几何联系对 $q\ge16$ 推出相应基数下界，分母分别为 $\log 4$、$\log 16$。 |
| 第 14–15 节，一阶上同调 | [CubicCocycles](CubicCocycles.lean) 用交叉同态模上余边界定义 $H^1$。给定手稿的生成元与交换关系，一个符号因子给出从 $H^1$ 到系数空间的单射。加入标准表示的矩阵条件得到维数至多 2。三个不同符号因子，或两个符号因子加一个无共同不动向量的因子，给出消失。无符号项的维数界、正特征比较及完整迹误差采用纸面证明。 |
| 第 17 节，三次上界 | [CubicCovering](CubicCovering.lean) 对实际的 `ProjectiveBlocks` 形式化有限抽样。若每条非水平线遗漏至多 $(q+1)/3$ 个参数，$q\ge16$ 且 $q\equiv2\bmod3$，就有大小至多 $2\log q/\log3+8$ 的阻塞集。值集大小与手稿上界的 $-\log\log q/\log 3$ 修正见第 17 节。 |

## 复现与验证记录

[CubicCertificate](CubicCertificate.lean) 的分块归约让内核分别检查候选表各块，再合并筛选结果与计数。模 41、47 沿用原有的逐线语义定理。32 元域六次证书从两个固定参数开始，按其余参数的取舍递归验证六元集，最小值的证明只需一个七元见证。

[GitHub Actions 工作流](../.github/workflows/verify.yml) 在 Ubuntu 上直接执行 `python3 checks/verify_lean.py`，再运行五个 Python 有限检查。本地复现时，在仓库根目录先进入 `lean/` 运行 `lake exe cache get`，然后回到根目录运行 `python checks/verify_lean.py`。脚本执行 `lake build`，重放入口的每条 `#print axioms`，检查所有源码模块均在入口导入闭包内，再以 Lean 自带的公理收集器递归追踪所有安全声明和带源码位置的不安全声明。编译器产生的无源码不安全辅助符号不单独用作根。从根出发的依赖闭包全量检查。允许的公理是 `Classical.choice`、`Quot.sound`、`propext`。

[verification.txt](verification.txt) 记录逐定理结果以及所有 Lean 源码、工具链和锁文件的 SHA-256。输入规范为 LF 换行，Linux 与 Windows 可以对照同一记录。修改源码后运行 `python checks/verify_lean.py --write`，审阅新的哈希与公理差异并与源码一同提交。[验证程序](../checks/verify_lean.py)
