# 手稿的 Lean 陈述与证明

工程使用 Lean 4.8.0，mathlib 固定在 `b5eba595428809e96f3ed113bc7ba776c5f801ac`。最小值使用 `IsLeast`，同时表达参数集的存在性和对所有参数集的下界。[固定次数篇](../Manuscript.pdf) · [变次数篇](../VariableDegree.pdf) · [纸面证明审阅记录](../REVIEW.md) · [构建入口与公理清单](BlockingCurves.lean) · [锁文件](lake-manifest.json)

Lean 源码注释沿用 [75326b5 合订稿节号](https://github.com/Heinz1729/monomial-blocking-curves/blob/75326b5091df2a99b4c9e0354d1e7292ee5d61bb/Manuscript.html)。下表采用现行两篇手稿的节号。原 §7–18 对应第一篇 §2–13，原 §21 对应第一篇 §14，原 §19、20、22 分别对应第二篇 §4、5、6。

## 从原问题到形式陈述

| 审阅问题 | 独立可查的接口 |
| --- | --- |
| 是否表达原文的阻塞问题？ | [ProblemStatement](ProblemStatement.lean) 只导入 mathlib，直接定义射影化的点与直线、关联关系、次数恰为 $d$ 的几何不可约齐次曲线、定义 1.1 的曲线族与问题 5.4 的最小值，并保留值集条件。[StatementComparison](StatementComparison.lean) 验证任意坐标代表的关联与曲线方程，`AGY_minimum_iff` 将原始最小值与 [Projective](Projective.lean) 的齐次坐标陈述等同。[AGY 原文](https://arxiv.org/html/2510.15332v2) |
| 曲线几何不可约吗？ | [GeometricIrreducibility](GeometricIrreducibility.lean) 在三个变量的多项式环中构造原式，核验总次数意义下的齐次性、求值为零的等价式、标量扩张到代数闭包后的不可约性。 |
| 何时是非平凡阻塞集？ | [NontrivialPencil](NontrivialPencil.lean) 证明对所有次数至少 2 的曲线并，不含整条有理直线当且仅当参数集为真子集。在 Frobenius 情形给出可达的非平凡最小值和全域退化判据。 |
| scattered 是否对应文献术语？ | [ScatteredComparison](ScatteredComparison.lean) 将非零向量的相同斜率条件与 [GeneralGeometry](GeneralGeometry.lean) 的核维数条件等同。[Zanella，§1](https://arxiv.org/abs/1909.07802) |
| 不同有限域模型的结论如何互用？ | [FieldTransport](FieldTransport.lean) 经域同构搬运任意参数集的阻塞谓词及最小值。[PrimeFieldInstances](PrimeFieldInstances.lean) 在与第二篇定理 1 相同的 `GaloisField` 接口上陈述 41、47 两个结论。 |

这些比较来自同一工程。数学文献给出陈述的外部来源，等价证明、复现脚本和 CI 的维护责任均在本仓库。外部审阅者可仅对照 `ProblemStatement.lean` 和原文检查问题的翻译。

## 定理入口

| 手稿 | 从陈述追到证书 |
| --- | --- |
| 第二篇定理 1 与定理 2 | [Paper](Paper.lean) 的 `projective_prime_power_minimum` 经 [Frobenius](Frobenius.lean) 和 [MainResult](MainResult.lean) 化为仿射超平面阻塞数。[LowerBound](LowerBound.lean) 与 [UpperBound](UpperBound.lean) 证明上下界。[GeneralGeometry](GeneralGeometry.lean) 证明 scattered 的充要刻画。 |
| 八元域 | [F8Example](F8Example.lean) 核验位运算与 256 个掩码。[F8Semantics](F8Semantics.lean) 将这些掩码与八元域全部参数集双射，逐集保基数和阻塞性。`projective_optimal_count` 在 `GaloisField 2 3` 上计得 56 个四元最优集。 |
| 三十二元域，六次 | [域运算与参数行](Sextic32.lean) 和[归一化六元集枚举](Sextic32Search.lean) 给出无解证书和一个七元见证。[位表语义](Sextic32Geometry.lean) 与[全局最小值](Sextic32Global.lean) 将证书搬运到 `GaloisField 2 5`。七元最优集总数和仿射轨道由[两种 Python 穷举](../checks/sextic32.py)逐集交叉核对。 |
| 计算附录，模 41 | [位表](Cubic41.lean) → [逐线方程](Cubic41Semantics.lean) → [归一化](CubicSymmetry.lean) → [全局最小值](CubicGlobal.lean) 与 [328 个最优集](CubicOrbit.lean)。 |
| 计算附录，模 47 | [位表](Cubic47.lean) → [逐线方程](Cubic47Semantics.lean) → [归一化](Cubic47Symmetry.lean) → [全局最小值](Cubic47Global.lean) 与 [轨道及稳定子](Cubic47Orbit.lean)。两锚点枚举覆盖 990 个四元和 14,190 个五元候选。 |
| 第一篇 §2–5 的三次避碰引理 | [CubicSlope](CubicSlope.lean) 核验有理临界值的方程及由差集条件选出无碰撞斜率。单值、迹估计和对数定理的证明见手稿。 |

## 渐近证明的形式化范围

| 结论 | Lean 的证明 | 仍需提供的数学输入 |
| --- | --- | --- |
| 第一篇 §6，存在错排 | [二重传递群的陪集](FrobeniusCoset.lean)一定含错排。[数值阈值](CubicAsymptotics.lean)由亏格界推出。 | 一般次数的单群直积、几何亏格估计及扭曲下降。 |
| 三次上界，无条件 | [CubicValueSet](CubicValueSet.lean) 将同值的有序根对计入 $x^2+xy+y^2=m$。过一个有理点的割线和切线给出至多 $q+1$ 个点。二根纤维补入重根对应的对角点，逐纤维求和得 $3M\le q+1$。[cubic_minimum_upper](CubicCovering.lean) 在原射影陈述上证明 $B(q,3)\le2\log q/\log3+8$。 | 域阶条件 $q\equiv2\bmod3$，对数式另需 $q\ge16$。 |
| 第一篇 §12，双线与双参数计数 | 非水平线恰遗漏 $h=(q+1)/3$ 个参数。固定两个非零斜率及第一条线的截距，双线共同遗漏数对第二个截距求和为 $h^2$；在不同平行线中求和为 $h(h-1)$。固定两个不同参数，全斜率下共同遗漏它们的线数恰为 $h(h-1)$。任意两线共同命中参数数目至少为 $(q-2)/3$。[CubicDoubleMiss](CubicDoubleMiss.lean) | 只需 $q\equiv2\bmod3$。$\mathbb F_5$ 中不同平行线对的共同遗漏数可为 0 或 1。[直接计数](../checks/cubic_pairs.py) |
| 第一篇 §12，取样、分支与专化 | 双计数给出遗漏线数的取样预算。逐阶 Newton 提升在 Laurent 级数域内构造同一分支，添入 $t$ 个根的次数至多为 $3^t$。在参数正则的有理位取剩余，便得到同时命中这些线的参数。[补点](CubicAlteration.lean) · [级数方程](CubicRepairChart.lean) · [实际分支](CubicRepairBranch.lean) · [次数](CubicRepairDegree.lean) · [专化](CubicRepairPlaces.lean) | 无条件。分支构造要求 $3\ne0$，由 $q\equiv2\bmod3$ 保证。 |
| 第一篇 §12，亏格与纤维 | 空根集和单根的函数域都具有零维正则微分空间。参数的每个有理纤维（含极点纤维）均满足扩张次数界，故有理位总数有限。[亏格](CubicRationalGenus.lean) · [极点](CubicPoleDegree.lean) · [有限纤维](CubicFiniteFibres.lean) | 无条件。 |
| 第一篇 §12–13，含负 $\log\log q$ 项的上界 | 令 $L=\log q$。对 $q\equiv2\bmod3$，包括特征 2，$L\le3^9$ 时，射影最小值满足 $B(q,3)\le(2L-\log L)/\log3+17$。任意域阶上也已证出由两项几何输入到同一不等式的蕴含。[取整与预算](CubicAlterationSize.lean) · [射影最小值](CubicLogLog.lean) | 有限范围无条件。第一篇 §12 的全域结论使用下文的 Castelnuovo–Severi 与 Hasse–Weil 输入。两者只用于至少三条线且通过严格点数阈值的残余线族。 |
| 两个开集及特征标，无条件 | [CubicUnramified](CubicUnramified.lean) 核验开集上的三次式可分；[CubicRationalRoots](CubicRationalRoots.lean) 把两种实际根数接到几何根的 Frobenius 不动点。[CubicCharacters](CubicCharacters.lean) 展开无根示性函数，非平凡张量总秩恰为 $4^\ell-1$。 | 只使用各定理列明的域和开集条件。 |
| 满直积及顶维项 | [CubicMonodromy](CubicMonodromy.lean) 从逐因子传递性和各坐标中独立支撑的惯性对换证明满直积，再用实际 $S_3^\ell$ 上的特征标正交性得到非平凡张量的平均值为零。 | 将具体覆盖的几何群作用识别为满足这两条局部性质的作用；用对偶把顶维重数识别为不变量重数。 |
| 第一篇 §9，群上同调 | [CubicCocycles](CubicCocycles.lean) 和 [CubicUnsigned](CubicUnsigned.lean) 直接对交叉余循环模余边界的 $H^1$ 作线性代数。非平凡无符号张量满足 $b_1\le4\ell+2$；有一个符号时至多 2，有两个符号且其余全平凡时至多 1，其余多符号情形消失。 | 子午圈生成元、异指标交换关系、各因子的局部矩阵作用。逐张量及总 Betti 数的上界均由 Lean 推出。 |
| 第一篇 §7–11，曲面下界 | [trace_deviation_of_spectra](CubicSurfaceTrace.lean) 从逐项数据推出第一篇式 (7.1)，再对真实阻塞集推出 $(\log q-2\log\log q)/\log4-5$ 的严格下界。 | `SurfaceLaws` 列出迹公式、仿射消没、顶维对偶、驯 Euler 特征、正特征比较与对偶，以及二、三阶 Frobenius 特征值的权界；另需上述局部单值模型。 |
| 第一篇 §13，固定斜率下界 | [fixed_deviation_of_curve_data](CubicCurveTrace.lean) 在每个字上用导子与权一估计，再求和得到固定斜率误差，推得分母 $\log16$ 的严格下界。库内还证出特征 2 的有限临界值与局部式 $Z^2(1+Z)$。 | `CurveLaws` 列出迹公式、Grothendieck–Ogg–Shafarevich 公式、顶维对偶、无穷远驯分歧、有限点的 Swan 导子等式及权一界；另需局部单值模型。 |

两个下界接口都以复数特征值和维数表达经典定理的数值结论。将这些数据实现为具体覆盖的 étale 上同调，并验证各条几何输入，仍依赖手稿证明。

## 变次数和分斜率上界

| 手稿结论 | Lean 核验范围 | 证明入口 |
| --- | --- | --- |
| 第二篇 §4，$\tau_q(d)$ 与 $B(q,d)$ 的差 | **无条件。** 有序碰撞中的每个比值至多对应 $h=\gcd(d-1,q-1)$ 个差值。任意水平覆盖可扩充，且新增参数至多为 $\lceil2\log q/\log(1+1/h)\rceil$。分两类斜率同时取样还给出一个取两项最大值的无条件界。 | [碰撞与射影最小值](PencilCollisionCover.lean) · [两类斜率](PencilHorizontal.lean) |
| 第二篇 §4，$B/\tau\to1$ | 幂值集按指数 $r=\gcd(d,q-1)$ 归约已证。代入 Zhou–Wu 命题 4.1 的水平下界后，Lean 给出相对误差及序列极限。 | [相对界与极限](PencilVariableGrowth.lean) · [有界指标的对数双边界](PencilBoundedIndices.lean) |
| 第二篇 §5，对任意 $n\ge2,m\ge1$，$B(s^n,mD)=s^{n-1}\tau_s(m)$ | **无条件。** 入口采用原来的商指数、射影最小值与非平凡性定义。$n\ge4$ 使用独立陪集平移。$n=3$ 以无根三次式实现零迹和任意范数。$n=2$ 由标量伸缩、范数碰撞密度与九个小奇数域的内核证书覆盖。 | [总定理](NormPowerMinimum.lean) · [独立平移](NormSamplingMinimum.lean) · [三次扩张](NormCubicMinimum.lean) · [二次小域](NormSmallOdd.lean) |
| 第一篇 §14，驯情形的 $2/\log(1/\delta_d)$ | 真实分裂域的 Frobenius 有不动点当且仅当纤维有有理根。水平遗漏数、例外纤维的上界和系数趋于 2 都无条件。非水平主项以逐共轭类有效 Chebotarev 估计为输入。 | [真实 Frobenius 作用](PencilFrobeniusCount.lean) · [有限取样预算](PencilAsymptotic.lean) |
| 第一篇 §14.1，坏特征的非水平遗漏与负 $\log\log q$ 项 | 离对角碰撞数等于实际仿射 Kummer 曲线点数，其差分多项式的次数与几何单根已证。$1/2+O_d(q^{-1/2})$ 使用该曲线的经典点数估计。一般 $p\nmid d$ 的共同补点使用实际函数域上的 Castelnuovo–Severi 与 Hasse–Weil。 | [Kummer 碰撞](PencilCharacterCollisions.lean) · [Laurent 分支与亏格](PencilRepairBranchGeometry.lean) · [完整取样与补点推导](PencilPaperBounds.lean) |

小奇数域证书枚举底域判别式，并将九个具体域模型的结果传输到任意同阶域。Python 独立程序直接枚举二次扩域的坐标，检查 26,960 组指数与非零斜率。[内核判据](NormSmall.lean) · [射影语义](NormSmallMinimum.lean) · [独立枚举](../checks/norm_quadratic.py)

## 扩张次数的整除二分律

第二篇定理 5 取 $q=s^n$、$m\mid s-1$、$d=s+(q-1)/m$。下表中的“无条件”只保留相应数学陈述里的域阶和整除条件。[第二篇 §6](../VariableDegree.html#extension-dichotomy)

| 结论 | Lean 核验范围与入口 |
| --- | --- |
| 二次精确值，非整除侧上界，整除侧下界 | **无条件。** 全部奇数 $s$ 的二次射影最小值为 $s$，且幂映射是对合。所有 $m\nmid n$ 有 $B\le2m\log(2q)+1$，所有 $m\mid n$ 有 $B\ge 1+n(s-1)/m$。另已证 $m^2\mid s-1$ 时为置换。[二次最小值](PhaseQuadratic.lean) · [可逆分支与取样](PhaseBranches.lean) · [迹投影下界](PhaseTraceLower.lean) |
| 整除侧完整的 $\Theta_m(ns)$ | **无条件。** 对仿射取样得到固定方向的空交概率和奇异分支的横截计数。令 $A=1+2m^2$，当 $s\ge A^2$ 时 $4n+1$ 个区组足够；较小的底域由次数 $sm$ 的多项式给出单点下界。定理 `divisible_pencil_minimum_bounds` 在独立的射影最小值上合并两侧，显式上界为 $[2m(1+A^2)+1]ns$。[方向二阶矩](PhaseDirectionSampling.lean) · [奇异分支](PhaseDividingUpper.lean) · [区组取样](PhaseBlockCover.lean) · [单点补界](PhasePointCover.lean) · [双边主定理](PhaseDividingMinimum.lean) |
| 大 $n$ 的共同换元与退化分支 | 已证明存在同一斜率，使全部分支可逆或只剩唯一退化分支。实际候选清单的总数至多为 $2m\ell$。所有有理原像的等价式、奇异纤维的 $0$ 或 $s$ 个原像、错配特征值给出真实漏线、乘积核的内直和、候选零点的单坐标条件均已证。实际候选多项式的可分性和用根重数排除 $m$ 次幂的判据单列。[实际纤维与漏线](PhaseCommonVariable.lean) · [本征空间](PhaseEigenFibres.lean) · [多项式与重数](PhaseRootMultiplicity.lean) |
| 有界 $n$ 的切片 | **无条件的代数步骤。** 对所选范数，Lean 证明不同的 Frobenius 共轭逆算子不成比例，包含 $n=2$ 的特殊比较。对不同的归一化仿射映射，沿任意给定非零方向可同时分开全部根，其条件为指标数的平方小于 $s$。[算子刚性](PhaseConjugateOperators.lean) · [固定方向避碰](PhaseNormSlice.lean) |
| $\ell$ 随 $\log q$ 增长的非整除侧下界 | **从逐项字符和估计到正计数的条件式定理。** 对真实乘法特征的 $M$ 个指定值，若每个非平凡完整和至多为 $W$，删去 $Z$ 个异常参数，计数与 $Q/m^M$ 的差至多为 $W+2Z$。两段参数预算直接给出正则见证。该行记录 §6 的通用计数引理。§7 的系数表定理已构造两类具体多项式，并从一元乘法字符 Weil 界推导出实际最小值下界，详见下表。显式域阶阈值 $\log q\ge16384m^5$ 同时保证切片有足够空间及主项超过误差。[字符正交展开](PhaseCharacterOrthogonality.lean) · [一致数值阈值](PhaseCharacterBudget.lean) |

## 第一篇 §12 的函数域输入

设 $F=\mathbb F_q$，$K/F(t)$ 为为每条残余线添入相应三次方程的一个根得到的 Laurent 分支，$K_S$ 为只添入 $S$ 中各根的子域。$K$ 及每个 $K_S$ 的全常数域均为 $F$。Lean 已识别 $K_{S\cup T}$ 内两个真实子域的合成以及两侧的相对次数。[Laurent 分支](CubicRepairBranch.lean) · [子域与相对次数](CubicStageFields.lean)

**亏格。** 对函数域 $E$，取每个正规、有限型、分式域为 $E$ 的仿射 $F$-代数 $A$，在 $\Omega_{E/F}$ 内求各 $\Omega_{A/F}$ 像的交。`regularForms` 给出这个子空间。对 $E=F(x)$，在 $x$ 和 $1/x$ 两个多项式坐标上同时正则的微分只能为零。保持 $F$ 的同构将这一计算用于实际的 $K_\varnothing$ 和 $K_{\{i\}}$。`regularFormsEquiv` 沿 $F$-代数同构传输正则微分，`full_stage_genus` 据此识别末阶段和 $K$ 的亏格。对多根子域，`CompositumBound` 用基数意义的秩陈述 Castelnuovo–Severi。归纳先推出正则微分空间有限维，再用其自然数维数估计亏格。[正则微分](CubicRationalGenus.lean) · [同构传输](CubicGenusTransport.lean) · [分支亏格界](CubicRepairGeometry.lean)

**有理位。** 有理位由赋值环及固定 $F$ 的剩余映射表示。对任意有限个不同的有理位，Lean 构造剩余值矩阵为单位阵的函数。在 $t=\infty$ 处，将关系除以次数最大的非零有理函数系数，所得系数同时正则。在 $t=a\in F$ 处，清分母后逐位取剩余可得所有多项式系数在 $a$ 消失，同时约去 $X-a$ 便降低任一非零系数的次数。线性无关性给出每个纤维的基数上界 $[K:F(t)]$，求和得到 $\#\mathrm{Place}(K)\le(q+1)[K:F(t)]$。这里每个有理位只计一次。[剩余值插值](CubicPoleFibre.lean) · [极点处的归一化](CubicPoleScalars.lean) · [线性无关与极点纤维](CubicPoleDegree.lean) · [有理位总数](CubicFiniteFibres.lean)

锁定版 mathlib 的 `Ideal.sum_ramification_inertia` 在 Dedekind 域及其有限整闭包上计算素理想的 $\sum e_Pf_P$。要用这一定理计算函数的极点除子次数，须在 $1/t$ 坐标的整闭包中把相关素理想与极点对应，并识别分歧指数和剩余次数。[mathlib 4.8 的定理及假设](https://github.com/leanprover-community/mathlib4/blob/b5eba595428809e96f3ed113bc7ba776c5f801ac/Mathlib/NumberTheory/RamificationInertia.lean#L808)

**Castelnuovo–Severi。** 对单根扩张 $E=B(x)$，令 $n_1=[E:B]$。Lean 用实际幂基证明了 $\bigoplus_{j<n_1}U\hookrightarrow V$，其中 $U\subset B$、$V\subset E$ 是 $F$-子空间，且 $x^jU\subset V$。将 $U,V$ 实现为大次数除子的 Riemann–Roch 空间，还须证明上述包含、拉回除子的次数公式和计入重数及剩余次数的极点除子次数。给定两条非特殊范围的 Riemann–Roch 维数等式和极点代价界，Lean 推出 $g_E\le n_1g_B+(n_1-1)(n_2-1)$，其中应用时 $n_2=[E:F(x)]$。Tau Ceti 已在 Lean 4.36.0-rc2 形式化完美常数域上的一般定理。用于本工程仍须将其函数域与亏格定义接到上述微分空间，并适配锁定的工具链。[幂基与维数比较](CubicCompositumRR.lean) · [Stichtenoth，第 3.11.3 定理](https://doi.org/10.1007/978-3-540-76878-4) · [Tau Ceti 定理源码](https://github.com/TauCetiProject/TauCeti/blob/04dc6d30e3935b9ea621d4ebb74d8ff2b0017a9b/TauCeti/FieldTheory/FunctionField/Consequences/Castelnuovo.lean)

**Hasse–Weil。** `CurveLaws` 的点数项使用上述全部有理位的基数。另一路径 `minimum_upper_of_weil_roots` 用赋值环按剩余次数逐阶构造 Euler 乘积，证明一次项等于实际有理位数。若各个次数的闭位集有限，且 $(1-T)(1-qT)Z(T)=\prod_{j=1}^{2g}(1-\beta_jT)$、各倒根满足 $\lvert\beta_j\rvert\le\sqrt q$，取一次项并对倒根实部用三角不等式，得到双侧估计 $\lvert\#\mathrm{Place}(K)-(q+1)\rvert\le 2g\sqrt q$。补点只需其下界。一次闭位与有理位的等价已证。各高次闭位集有限及上述分解和权界由该路径显式传入。AxiomMath/Weil 在 Lean 4.34.0-rc2 给出了光滑固有几何不可约概形的 zeta 分解与权界。接入该结果还须为 $K$ 实现相应的曲线模型，将其闭点与赋值环对应，并证明一次上同调给出的分子次数等于这里的 $2g$。[Euler 乘积与一次项](CubicZetaPoints.lean) · [条件式上界](CubicLogLog.lean) · [AxiomMath/Weil 的定理接口](https://github.com/AxiomMath/Weil/tree/27cdb2049be6#3-riemann-hypothesis-delignes-theorem)

## 尖点三次与一般系数表

| 手稿 | Lean 已核验 | 纸面输入 |
| --- | --- | --- |
| 第一篇 §15 | 尖点曲线齐次射影阻塞与试根的等价、原族阻塞参数对新族的涵盖，以及非水平漏线与旧有序对的精确计数。$\log q\le3^9$ 时的次阶上界无条件。 | 实际漏线数的迹估计使用 §10 原有的逐项几何输入。十一元域的两个精确最小值由 Python 穷举。[曲线与计数](CuspidalTransfer.lean) · [有限检查](../checks/cubic_pairs.py) |
| 第二篇 §7 | 整除侧的实际最优集与匹配上下界，非整除侧对数上界。精确阶字符、重复标签、全体有理原像、两种多项式族的几何非幂与随参数数目增长的一致预算均有 Lean 证明。 | 非整除侧完整下界只依赖所选求和域上的一元乘法字符 Weil 界。[最小值定理](PiecewiseMinimum.lean) · [经典输入的精确签名](PiecewiseWeil.lean) |

### 定理 6 的证明路径

| 参数范围 | 已验证的结论与接口 |
| --- | --- |
| $h\mid n$ | 令 $A_m=1+2m^2$。两端由同一个最优参数集实现，$1+n(s-1)\le rB(f)$ 且 $B(f)\le [2m(1+A_m^2)+1]ns$。取样上界对全部系数表成立。[同步侧最小值](PiecewiseSyncUpper.lean) |
| $n\ge4m$ | 合并重复系数，给实际幂标号选择错误系数，计入唯一奇异分支的全部 $0$ 或 $s$ 个原像。实际候选数 $M\le2m\lvert S\rvert$。几何纤维逐坐标的根重数排除所有非平凡指数向量，包括合数 $m$。[纤维与斜率](PiecewiseFibres.lean) · [几何坐标](PiecewiseGeometric.lean) · [实际漏线](PiecewiseLargeEscape.lean) |
| $2\le n<4m$ | 构造同一斜率和同一底域直线用于所有平移。用实际逆算子构造次数 $n$ 的底域范数多项式并分开全部共轭根；由其私有单根得到几何非幂性。二次扩张的共轭互换也已排除。[斜率与根](PiecewiseNormSlice.lean) · [范数多项式](PiecewiseNormPolynomial.lean) · [底域上的漏线](PiecewiseBoundedEscape.lean) |
| $n=1$ | 分支系数给出遗漏的乘法陪集。对阻塞集大小 $\ell$，经典 Weil 输入推出 $q/m^\ell\le\ell(\sqrt q+2)$ 和半对数主项。[显式有限界](PiecewiseGroundEscape.lean) |
| $h\nmid n$ | $\log q\ge16384m^5$ 时，$\log q/(32m^2\log m)<B(f)\le2m\log(2q)+1$。[统一最小值](PiecewiseMinimum.lean) 按扩张次数选取唯一的外部数学输入。幂标号与精确阶复值字符的纤维对应，以及从逐个多项式的完整和界到整组指定字符值的推导均已形式化。[字符构造](PiecewiseCharacter.lean) · [误差与阈值](PiecewiseWeil.lean) |

## 复现与验证记录

[CubicCertificate](CubicCertificate.lean) 逐块核验输入覆盖、输出拼接或计数之和。模 41、47 的行表和候选筛选每块取 4 个外层索引。32 元域的 1,024 行分 8 块，27,405 个归一化六元候选再按首个自由参数分 27 片。各片由内核 `decide` 核验，归纳引理将它们接回原始射影定理。

在 Linux 上从空的本项目 `.lake/build` 复现时，可复用锁定的 mathlib 缓存。执行 `ulimit -s` 查看当前主线程栈限制，然后在仓库根目录运行 `python3 checks/verify_lean.py --serial`。提交 `6d61b6d` 曾在本地 Debian 把默认 8192 KiB 的软栈上限同时设为硬上限，依次通过 `--serial --write` 与 `--serial`。该次 Linux 与 Windows 的验证记录逐字节一致。当前提交的点名定理与文件哈希见下方验证记录。托管工作流会打印其默认栈限制。

[GitHub Actions 工作流](../.github/workflows/verify.yml) 在 Ubuntu 上执行同一条串行审计命令，再运行八个 Python 有限检查。首次安装依赖时，可在 `lean/` 运行 `lake exe cache get` 下载锁定的 mathlib 缓存。脚本执行 `lake build`，重放入口的每条 `#print axioms`，检查所有源码模块均在入口导入闭包内，再以 Lean 自带的公理收集器递归追踪所有安全声明和带源码位置的不安全声明。编译器产生的无源码不安全辅助符号不单独用作根。从根出发的依赖闭包全量检查。允许的公理是 `Classical.choice`、`Quot.sound`、`propext`。

[verification.txt](verification.txt) 记录逐定理结果以及所有 Lean 源码、工具链和锁文件的 SHA-256。输入规范为 LF 换行，Linux 与 Windows 可以对照同一记录。修改源码后运行 `python checks/verify_lean.py --write`，审阅新的哈希与公理差异并与源码一同提交。[验证程序](../checks/verify_lean.py)
