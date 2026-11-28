# 成果与核验状态

状态按具体数学陈述标注。同一篇论文可以同时包含下列三类结果。

| 标记 | 阅读方式 |
| --- | --- |
| **Solved** | 在陈述写明的域、次数等假设下，Lean 已证明结论。全仓公理白名单为 `Classical.choice`、`Quot.sound`、`propext`。 |
| **Conditional** | Lean 已证明从列出的经典数学输入到结论的推导。输入的证明范围可在对应模块的定理签名中核查。 |
| **Open** | 注明是本仓库尚缺的形式化步骤，还是手稿仍未确定的数学问题。 |

## 第一篇 · 固定次数与尖点族

| 状态 | 结果 | 证明入口 |
| --- | --- | --- |
| **Solved** | 两族的射影陈述、几何不可约性及同域比较。次数为 $`d=s`$ 时，在 $`q=s^2`$ 上，尖点族和图像族的最小值分别为 $`3`$ 和 $`2s-1`$。在 $`q=s^3`$ 且 $`s\ge4`$ 时，分别为 $`4`$ 和 $`3s-2`$。 | [射影陈述](lean/ProblemStatement.lean) · [尖点几何](lean/CuspidalGeometry.lean) · [两组精确值](lean/CuspidalNormMinimum.lean#L129) |
| **Solved** | 尖点族在实际分裂域的逐根塔、次数界、野惯性的单坐标作用和 Frobenius 陪集。各坐标根的共同周期界只依赖次数。 | [逐根次数](lean/CuspidalRootDegrees.lean) · [单坐标作用](lean/CuspidalSheetAction.lean) · [陪集](lean/CuspidalGeometricFrobenius.lean) |
| **Solved** | 在实际复合分裂域构造扭曲的不动域。扩常数恢复原覆盖，覆盖次数和几何亏格相等。每个有理纤维的点数受覆盖次数控制。在每个好有理位置，特化纤维的 Frobenius 根置换与所选陪集元的根置换，在每个坐标的对称群中分别共轭。这足以将所有坐标同时无不动点的性质传给特化纤维。 | [扭曲的常数域与亏格](lean/CuspidalTwistGenus.lean) · [纤维次数](lean/CubicFiniteFibres.lean) · [根的特化](lean/CuspidalRationalSpecialization.lean) |
| **Conditional** | 固定 $`d\ge3`$ 的尖点族全特征对数下界。对 $`0\lt c\lt 1/(2\log(d!))`$，只需塔上的 Castelnuovo–Severi 不等式与下降域的 Hasse–Weil 下界，即得到适用于全部平移集的域阶阈值。 | [定量及渐近陈述](lean/CuspidalDescendedLower.lean#L53) |
| **Open · 形式化** | 在本库的正则微分与有理位置定义下，无条件证明上述两个曲线不等式。若要比较下降前后的内蕴正则微分维数，还需光滑射影模型的微分基变换定理；当前下界直接使用几何亏格。 | [逐层亏格估计](lean/CuspidalCompositumGenus.lean) · [Lean 索引](lean/README.md) |
| **Open · 形式化** | 手稿给出了图像族在每个固定 $`d\ge2`$ 下的全特征对数下界证明。Lean 已证明二重传递群的陪集含错排，以及增长窗口的数值估计。一般次数的几何群、亏格及好纤维的存在仍须接到实际图像族的射影阻塞数。 | [论文中的全特征证明](papers/FixedDegreePencils.tex#L151) · [陪集错排](lean/FrobeniusCoset.lean) · [增长窗口](lean/FixedDegreeBudget.lean) |
| **Conditional** | 奇特征三次图像族在 $`q\equiv2\pmod3`$、$`q\ge16`$ 时的双参数下界，首项系数为 $`1/\log4`$。Lean 对每个平移集从 `SurfaceSpectrum` 和 `SurfaceLaws` 推出含次项的显式不等式。这些输入包括实际几何群上的惯性作用、正特征比较、逐特征标迹公式和权界。 | [几何输入](lean/CubicSurfaceTrace.lean#L307) · [射影阻塞集下界](lean/CubicSurfaceTrace.lean#L395) |
| **Open · 数学问题** | 三次置换族阻塞数除以自然对数后的最优首项常数。现有上下界仍有间距。 | [第一篇的上下界](README.md#一般次数与精确值) |

## 第二篇与有限证书

| 状态 | 结果 | 证明入口 |
| --- | --- | --- |
| **Solved** | 任意有限域扩张 $`\mathbb F_s\subset\mathbb F_q`$，若 $`q=s^n`$、$`n\ge2`$、$`m\ge1`$，则 $`B(q,mD)=s^{n-1}\tau_s(m)`$，其中 $`D=(q-1)/(s-1)`$，$`\tau_s(m)`$ 为底域中幂值集的最少加法平移覆盖数。每个最优集给出的阻塞集均不含整条有理直线。 | [范数幂最小值](lean/NormPowerMinimum.lean#L46) · [非平凡性](lean/NormPowerMinimum.lean#L58) |
| **Solved** | 对分段 Frobenius 族，系数周期整除扩张次数时的匹配上下界，以及非整除时的对数上界，均已有 Lean 证明。分圆单项式的 $`m=n=2`$ 特例在每个奇数阶底域上满足 $`B=s`$。 | [同步侧最小值](lean/PiecewiseSyncUpper.lean#L165) · [非同步侧取样上界](lean/PiecewiseFrobenius.lean#L255) · [二次精确值](lean/PhaseQuadratic.lean#L206) |
| **Conditional** | 分段 Frobenius 族非同步侧的对数下界。Lean 已处理重复系数与退化分支的全部有理原像。若 $`\log q\ge16384m^5`$，从相应求和域上的一元乘法特征 Weil 界推出射影计数所用的图像阻塞最小值下界。 | [字符和](lean/PiecewiseWeil.lean) · [输入与最小值](lean/PiecewiseMinimum.lean#L48) |
| **Solved** | 域阶 8、32、41、47 的四个最小值，以及域阶 8、41、47 的最优解数。 | [有限证书附录](FiniteCertificates.pdf) · [审计入口](lean/BlockingCurves.lean) |
| **Open · 形式化** | 域阶 32 的 10,912 个最优集及 11 个仿射轨道已有两种穷举交叉核对，完整分类仍待 Lean 证书。 | [计算程序](checks/sextic32.py) |

逐定理的域阶限制、输入和公理记录见 [Lean 索引](lean/README.md) 与 [验证记录](lean/verification.txt)。两份中文手稿、英文论文及其可编辑源码由[仓库首页](README.md)统一索引。
