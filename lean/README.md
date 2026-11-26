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

| 结论 | Lean 的证明 | 仍需提供的数学输入 |
| --- | --- | --- |
| 第 11 节，存在错排 | [二重传递群的陪集](FrobeniusCoset.lean)一定含错排。[数值阈值](CubicAsymptotics.lean)由亏格界推出。 | 一般次数的单群直积、几何亏格估计及扭曲下降。 |
| 三次上界，无条件 | [CubicValueSet](CubicValueSet.lean) 将同值的有序根对计入 $x^2+xy+y^2=m$。过一个有理点的割线和切线给出至多 $q+1$ 个点。二根纤维补入重根对应的对角点，逐纤维求和得 $3M\le q+1$。[cubic_minimum_upper](CubicCovering.lean) 在原射影陈述上证明 $B(q,3)\le2\log q/\log3+8$。 | 域阶条件 $q\equiv2\bmod3$，对数式另需 $q\ge16$。 |
| 第 17 节，双线与双参数计数 | 非水平线恰遗漏 $h=(q+1)/3$ 个参数。固定两个非零斜率及第一条线的截距，双线共同遗漏数对第二个截距求和为 $h^2$；在不同平行线中求和为 $h(h-1)$。固定两个不同参数，全斜率下共同遗漏它们的线数恰为 $h(h-1)$。任意两线共同命中参数数目至少为 $(q-2)/3$。[CubicDoubleMiss](CubicDoubleMiss.lean) | 只需 $q\equiv2\bmod3$。$\mathbb F_5$ 中不同平行线对的共同遗漏数可为 0 或 1。[直接计数](../checks/cubic_pairs.py) |
| 第 17 节，取样、分支与专化 | [CubicAlteration](CubicAlteration.lean) 双计数样本与遗漏线，证明补一个参数的结论。[CubicRepairChart](CubicRepairChart.lean) 用逐阶 Newton 提升构造常项为 1 的唯一形式级数根；[CubicRepairBranch](CubicRepairBranch.lean) 在 Laurent 级数域内构造实际分支并核验全常数域。[CubicRepairDegree](CubicRepairDegree.lean) 给出添根次数界 $3^t$；[CubicRepairPlaces](CubicRepairPlaces.lean) 证明单根子域有理，且在非极点有理位专化得到公共命中参数。 | 这些代数与有限组合步骤无条件。分支构造要求 $3\ne0$，由域阶条件自动满足。 |
| 第 17–18 节，含负 $\log\log q$ 项的上界 | [CubicAlterationSize](CubicAlterationSize.lean) 证明取整、参数预算及严格点数阈值。[CubicLogLog](CubicLogLog.lean) 在独立射影最小值上证明 $B(q,3)\le(2\log q-\log\log q)/\log3+17$，包括特征 2。$\log q\le3^9$ 时，`minimum_upper_finite_range` 无条件成立。 | 任意 $q\equiv2\bmod3$ 的 `minimum_upper` 使用 `GeometryAt`。只需为至少三条线且通过严格点数阈值的残余线族提供输入；至多两条线可直接补齐（$q>2$）。对实际构造的分支，[CubicRepairGeometry.CurveLaws](CubicRepairGeometry.lean) 列明有理函数域亏格零、Castelnuovo–Severi 不等式、极点纤维的度数界、Hasse–Weil 界。 |
| 两个开集及特征标，无条件 | [CubicUnramified](CubicUnramified.lean) 核验开集上的三次式可分；[CubicRationalRoots](CubicRationalRoots.lean) 把两种实际根数接到几何根的 Frobenius 不动点。[CubicCharacters](CubicCharacters.lean) 展开无根示性函数，非平凡张量总秩恰为 $4^\ell-1$。 | 只使用各定理列明的域和开集条件。 |
| 满直积及顶维项 | [CubicMonodromy](CubicMonodromy.lean) 从逐因子传递性和各坐标中独立支撑的惯性对换证明满直积，再用实际 $S_3^\ell$ 上的特征标正交性得到非平凡张量的平均值为零。 | 将具体覆盖的几何群作用识别为满足这两条局部性质的作用；用对偶把顶维重数识别为不变量重数。 |
| 第 14 节，群上同调 | [CubicCocycles](CubicCocycles.lean) 和 [CubicUnsigned](CubicUnsigned.lean) 直接对交叉余循环模余边界的 $H^1$ 作线性代数。非平凡无符号张量满足 $b_1\le4\ell+2$；有一个符号时至多 2，有两个符号且其余全平凡时至多 1，其余多符号情形消失。 | 子午圈生成元、异指标交换关系、各因子的局部矩阵作用。逐张量及总 Betti 数的上界均由 Lean 推出。 |
| 第 12–16 节，曲面下界 | [trace_deviation_of_spectra](CubicSurfaceTrace.lean) 从逐项数据推出式 (12.1)，再对真实阻塞集推出 $(\log q-2\log\log q)/\log4-5$ 的严格下界。 | `SurfaceLaws` 列出迹公式、仿射消没、顶维对偶、驯 Euler 特征、正特征比较与对偶，以及二、三阶 Frobenius 特征值的权界；另需上述局部单值模型。 |
| 第 18 节，固定斜率下界 | [fixed_deviation_of_curve_data](CubicCurveTrace.lean) 在每个字上用导子与权一估计，再求和得到固定斜率误差，推得分母 $\log16$ 的严格下界。库内还证出特征 2 的有限临界值与局部式 $Z^2(1+Z)$。 | `CurveLaws` 列出迹公式、Grothendieck–Ogg–Shafarevich 公式、顶维对偶、无穷远驯分歧、有限点的 Swan 导子等式及权一界；另需局部单值模型。 |

两个下界接口都以复数特征值和维数表达经典定理的数值结论。将这些数据实现为具体覆盖的 étale 上同调，并验证各条几何输入，仍依赖手稿证明。第 17 节上界使用单独的函数域接口，见上表。

## 复现与验证记录

[CubicCertificate](CubicCertificate.lean) 逐块核验输入覆盖、输出拼接或计数之和。模 41、47 的行表和候选筛选每块取 4 个外层索引。32 元域的 1,024 行分 8 块，27,405 个归一化六元候选再按首个自由参数分 27 片。各片由内核 `decide` 核验，归纳引理将它们接回原始射影定理。

在 Linux 上从空的本项目 `.lake/build` 复现时，可复用锁定的 mathlib 缓存。执行 `ulimit -s` 查看当前主线程栈限制，然后在仓库根目录运行 `python3 checks/verify_lean.py --serial`。提交 `6d61b6d` 曾在本地 Debian 把默认 8192 KiB 的软栈上限同时设为硬上限，依次通过 `--serial --write` 与 `--serial`。该次 Linux 与 Windows 的验证记录逐字节一致。当前提交的点名定理与文件哈希见下方验证记录。托管工作流会打印其默认栈限制。

[GitHub Actions 工作流](../.github/workflows/verify.yml) 在 Ubuntu 上执行同一条串行审计命令，再运行五个 Python 有限检查。首次安装依赖时，可在 `lean/` 运行 `lake exe cache get` 下载锁定的 mathlib 缓存。脚本执行 `lake build`，重放入口的每条 `#print axioms`，检查所有源码模块均在入口导入闭包内，再以 Lean 自带的公理收集器递归追踪所有安全声明和带源码位置的不安全声明。编译器产生的无源码不安全辅助符号不单独用作根。从根出发的依赖闭包全量检查。允许的公理是 `Classical.choice`、`Quot.sound`、`propext`。

[verification.txt](verification.txt) 记录逐定理结果以及所有 Lean 源码、工具链和锁文件的 SHA-256。输入规范为 LF 换行，Linux 与 Windows 可以对照同一记录。修改源码后运行 `python checks/verify_lean.py --write`，审阅新的哈希与公理差异并与源码一同提交。[验证程序](../checks/verify_lean.py)
