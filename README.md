# 有限域上单项式曲线的竖直平移与阻塞数

在有限射影平面中，至少需要多少条曲线的竖直平移，才能使每条有理直线都与其中一条曲线相交？第一篇固定曲线次数，研究阻塞数随域阶的增长；第二篇让次数也变化，研究哪些曲线族有精确最小值，以及扩张次数如何改变增长阶。[AGY 问题 5.4](https://arxiv.org/html/2510.15332v2#S5) · [独立射影陈述](lean/ProblemStatement.lean)

**证明冻结于 [768cfbb](https://github.com/Heinz1729/monomial-blocking-curves/commit/768cfbb8db344f3e7749e5061370a7493321cca6)。** [完整研究时间线](TIMELINE.md) 按北京时间列出从首稿到冻结版的 21 次提交，逐次链接当时的手稿、证明或审计记录。[成果状态总览](STATUS.md) 汇集两篇的分类索引及共享有限证书。

| 状态 | 含义 |
| --- | --- |
| **Solved** | Lean 在列明的域、次数等假设下证明了这项结论。 |
| **Conditional** | Lean 证明了从所列数学输入到结论的推导。 |
| **Open** | 分别注明尚缺的 Lean 形式化步骤，以及手稿仍未解决的数学问题。 |

<a name="一般次数与精确值"></a>

## 第一篇 · 固定次数与尖点族

[第一篇目录与全部定理](papers/fixed-degree/README.md) · [中文 PDF](Manuscript.pdf) · [英文 PDF](papers/fixed-degree/FixedDegreePencils.pdf) · [LaTeX 源码](papers/fixed-degree/FixedDegreePencils.tex)

| 状态 | 代表性结果 | 手稿 | Lean 证明或已有步骤 |
| --- | --- | --- | --- |
| [Solved](papers/fixed-degree/README.md#solved) | 在同一域取相同次数 $`d=s`$。二次扩张上，尖点族和图像族分别需要 3 和 $`2s-1`$ 条；三次扩张且 $`s\ge4`$ 时分别需要 4 和 $`3s-2`$ 条。 | [定理 6](Manuscript.html#L261) | [二次比较](lean/CuspidalNormMinimum.lean#L129) · [三次比较](lean/CuspidalNormMinimum.lean#L140) |
| [Conditional](papers/fixed-degree/README.md#conditional) | $`p\gt3`$、$`q\equiv2\bmod3`$ 时，三次置换图像族下界的首项系数为 $`1/\log4`$。形式证明使用正特征曲面上的单值、迹公式与权界。 | [定理 3](Manuscript.html#L122) | [几何输入及下界](lean/CubicSurfaceTrace.lean#L395) |
| [Conditional](papers/fixed-degree/README.md#conditional) | 一般尖点族的全特征下界已归约到 Castelnuovo–Severi 与 Hasse–Weil 两项曲线不等式；下降与逐坐标特化已证。 | [定理 5](Manuscript.html#L244) | [实际有理位置的特化](lean/CuspidalRationalSpecialization.lean#L107) · [条件式下界](lean/CuspidalDescendedLower.lean#L61) |
| [Open](papers/fixed-degree/README.md#open) | **形式化。** 固定次数图像族的全特征下界已有纸面证明，实际野覆盖到下界的完整 Lean 推导仍缺。**数学问题。** 三次置换族的最优首项常数仍未知。 | [全特征定理](Manuscript.html#L78) · [首项常数](Manuscript.html#L167) | [陪集错排](lean/FrobeniusCoset.lean#L33) · [误差窗口](lean/FixedDegreeBudget.lean#L12) · [三次上界](lean/CubicCovering.lean#L148) |

<a name="次数随域阶增长"></a>
<a name="扩张次数的整除二分律"></a>
<a name="分段线性置换的系数判据"></a>

## 第二篇 · 变次数、范数幂与系数周期

[第二篇目录与全部定理](papers/variable-degree/README.md) · [中文 PDF](VariableDegree.pdf) · [英文 PDF](papers/variable-degree/CoefficientPeriods.pdf) · [LaTeX 源码](papers/variable-degree/CoefficientPeriods.tex)。中文稿包含定理 1–6，英文独立稿集中讨论定理 6 的系数周期及其应用。

| 状态 | 代表性结果 | 手稿 | Lean 证明或已有步骤 |
| --- | --- | --- | --- |
| [Solved](papers/variable-degree/README.md#solved) | 对 $`q=s^n`$、$`n\ge2`$、$`m\ge1`$，取 $`D=(q-1)/(s-1)`$，则 $`B(q,mD)=s^{n-1}\tau_s(m)`$，其中 $`\tau_s(m)`$ 是底域中幂值集的最少平移覆盖数。 | [定理 4](VariableDegree.html#L73) | [范数幂最小值](lean/NormPowerMinimum.lean#L46) |
| [Solved](papers/variable-degree/README.md#solved) | 分段 Frobenius 图像的系数周期整除扩张次数时，有匹配的上下界；非整除侧的对数上界也已证明。 | [定理 6](VariableDegree.html#L147) | [整除侧](lean/PiecewiseSyncUpper.lean#L165) · [非整除侧上界](lean/PiecewiseFrobenius.lean#L255) |
| [Conditional](papers/variable-degree/README.md#conditional) | 非整除侧取得匹配的对数下界还使用一元乘法特征 Weil 界。重复系数、退化分支的全部原像及随平移数增长的误差已纳入 Lean 推导。 | [字符和下界](VariableDegree.html#L157) | [精确输入](lean/PiecewiseMinimum.lean#L48) · [最小值](lean/PiecewiseMinimum.lean#L56) |
| [Open](papers/variable-degree/README.md#open) | **数学问题。** 所有非恒等置换单项式的统一上界能否从 $`O(\sqrt q\log q)`$ 降为 $`O(\sqrt q)`$？二次精确族已经达到平方根阶。 | [上界与问题](VariableDegree.html#L142) | [像集估计](lean/PencilCollisionCover.lean#L140) · [二次精确值](lean/PhaseQuadratic.lean#L206) |

## 证明审阅与复现

[四个有限域的最小值和轨道证书](STATUS.md#有限域证书) · [原始计算附录](FiniteCertificates.pdf) · [纸面证明审阅记录](REVIEW.md) · [Lean 声明与依赖索引](lean/README.md) · [全仓公理及哈希记录](lean/verification.txt)

在仓库根目录执行以下命令，可用锁定的 Lean 4.8.0 和 mathlib 复验全部声明。白名单为 `Classical.choice`、`Quot.sound`、`propext`。

~~~sh
(cd lean && lake exe cache get)
python3 checks/verify_lean.py --serial
~~~

[默认栈工作流](.github/workflows/verify.yml) · [冻结证明的成功运行](https://github.com/Heinz1729/monomial-blocking-curves/actions/runs/46117024003) · [独立有限计算](checks/) · [RMM 答卷（附录外）](bonus/RMM-2026-中文答卷.pdf)
