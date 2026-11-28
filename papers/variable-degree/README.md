# 第二篇 · 变次数单项式曲线的阻塞数

中文稿研究次数随域阶变化时的阻塞数 $`B(q,d)`$，从 Frobenius 幂和范数幂的精确值推到分段 Frobenius 图像的整除二分律。英文独立稿集中讨论中文定理 6 及其应用。

[中文全文 PDF](../../VariableDegree.pdf) · [中文手稿源码](../../VariableDegree.html) · [英文论文 PDF](CoefficientPeriods.pdf) · [英文 LaTeX 源码](CoefficientPeriods.tex) · [英文稿要点](CoefficientPeriods-highlights.txt)

以下沿用中文定理编号。定理 5、6 中 $`q=s^n`$，$`m\ge2`$ 且 $`m\mid s-1`$。定理 5 的单项式次数为 $`d=s+(q-1)/m`$。定理 6 在每个非零乘法陪集上取 $`f(x)=c_jx^s`$，至少使用两个不同的底域非零系数，允许重复。系数比生成的乘法子群的阶称为系数周期。

## Solved

下列结论已在 Lean 中证明。

| 结果 | 中文手稿 | Lean 证明 |
| --- | --- | --- |
| **定理 1 · Frobenius 幂。** 设 $`g=\gcd(h,e)`$、$`h,e\ge1`$，则 $`B(p^h,p^e)=1+(h/g)(p^g-1)`$。当 $`h\mid e`$ 时唯一的阻塞参数集是全域；其余情形可由非平凡阻塞集达到最小值。 | [公式与边界](../../VariableDegree.html#L27) | [射影最小值](../../lean/Paper.lean#L16) · [全域情形](../../lean/NontrivialPencil.lean#L42) · [非平凡情形](../../lean/NontrivialPencil.lean#L70) |
| **定理 2 · 线性化图像。** 一个底域线性映射是 scattered，当且仅当对每个参数集，图像阻塞等价于命中所有仿射超平面。底域阶为 $`Q`$、扩张次数为 $`n`$ 时，scattered 映射的最小值为 $`1+n(Q-1)`$。 | [充要条件](../../VariableDegree.html#L55) | [等价性](../../lean/GeneralGeometry.lean#L210) · [最小值](../../lean/MainResult.lean#L36) |
| **定理 3 · 从水平覆盖到射影阻塞。** 令 $`h=\gcd(d-1,q-1)`$。从任一水平覆盖出发，至多再加 $`\lceil 2\log q/\log(1+1/h)\rceil`$ 个参数即可命中所有斜率，对每个 $`d\ge2`$ 成立。 | [加项界](../../VariableDegree.html#L64) | [扩充既定覆盖](../../lean/PencilCollisionCover.lean#L194) · [最小值之差](../../lean/PencilCollisionCover.lean#L249) |
| **定理 4 · 范数幂。** 设 $`n\ge2`$、$`m\ge1`$、$`D=(q-1)/(s-1)`$。若 $`\tau_s(m)`$ 是底域幂值集的最小平移覆盖数，则 $`B(q,mD)=s^{n-1}\tau_s(m)`$。特别地 $`B(q,D)=s^{n-1}`$，每个最优集都给出非平凡阻塞集。 | [范数幂公式](../../VariableDegree.html#L73) | [一般幂](../../lean/NormPowerMinimum.lean#L46) · [范数](../../lean/NormPowerMinimum.lean#L52) · [非平凡性](../../lean/NormPowerMinimum.lean#L58) |
| **定理 5 · 分圆单项式。** $`m\mid n`$ 时上下界匹配，给出 $`B(q,d)=\Theta_m(ns)`$。$`m\nmid n`$ 时已有上界 $`B(q,d)\le 2m\log(2q)+1`$。 | [两侧陈述](../../VariableDegree.html#L89) | [整除侧双边界](../../lean/PhaseDividingMinimum.lean#L139) · [非整除侧上界](../../lean/PhaseBranches.lean#L399) |
| **推论 5.1 · 二次精确值与同域对照。** 对每个奇素数幂 $`s`$，$`m=n=2`$ 时有 $`B=s`$。在 $`q=t^6`$（$`t`$ 为奇素数幂）上，两种指数 $`(q-1)/2+t^3`$ 与 $`(q-1)/2+t^2`$ 都给出置换。前者的精确值为 $`t^3`$，后者的已证上界为 $`4\log(2q)+1`$。 | [二次精确值](../../VariableDegree.html#L132) · [同域对照](../../VariableDegree.html#L135) | [二次最小值](../../lean/PhaseQuadratic.lean#L206) · [同域比较定理](../../lean/PhaseQuadratic.lean#L228) |
| **定理 6 · 一般系数表。** 系数周期整除 $`n`$ 时有 $`B(f)=\Theta_m(ns)`$；不整除时上界仍为 $`2m\log(2q)+1`$。常数对系数表一致。 | [定理 6](../../VariableDegree.html#L148) · [同步侧的显式界](../../VariableDegree.html#L165) | [同步侧最小值](../../lean/PiecewiseSyncUpper.lean#L165) · [非同步见证](../../lean/PiecewiseMinimum.lean#L31) · [取样上界](../../lean/PiecewiseFrobenius.lean#L255) |

## Conditional

| 结论与所需输入 | 中文手稿 | Lean 定理与输入 |
| --- | --- | --- |
| **定理 3 的渐近推论。** 设 $`r=\gcd(d,q-1)\ge2`$、$`h=\gcd(d-1,q-1)`$，$`\tau_q(d)`$ 是水平覆盖最小值。在 Zhou–Wu 命题 4.1 的水平下界下，$`r,h`$ 有界时 $`B=\Theta(\log q)`$；若 $`(h+1)\log r=o(r)`$，则 $`B/\tau_q(d)\to1`$。 | [两个推论](../../VariableDegree.html#L69) | [有界指标](../../lean/PencilBoundedIndices.lean#L10) · [比值极限](../../lean/PencilVariableGrowth.lean#L125) |
| **定理 6 · 非同步侧下界。** 给定求和域上的一元乘法特征 Weil 界，且 $`\log q\ge16384m^5`$，Lean 证明 $`B(f)\gt\log q/(32m^2\log m)`$。与无条件上界合并即得 $`\Theta_m(\log q)`$。重复系数、唯一退化分支的全部原像及随平移数增长的误差均在此定理内处理。定理 5 的非整除侧是取恒等标号系数表的特例，中文 §6 另给单项式的证明。 | [单项式字符和](../../VariableDegree.html#L106) · [系数表的假设与结论](../../VariableDegree.html#L166) | [按扩张次数选求和域](../../lean/PiecewiseMinimum.lean#L48) · [实际最小值](../../lean/PiecewiseMinimum.lean#L56) |
| **底域上的更强下界。** 当 $`n=1`$ 时，同一 Weil 输入给出 $`q/m^\ell\le\ell(\sqrt q+2)`$，其中 $`\ell`$ 是阻塞集大小。因此下极限首项系数至少为 $`1/(2\log m)`$。 | [底域估计](../../VariableDegree.html#L163) | [有限界](../../lean/PiecewiseGroundEscape.lean#L151) · [半对数下界](../../lean/PiecewiseGroundEscape.lean#L181) |

## Open

| 类型与问题 | 中文手稿 | 可核查的 Lean 进展 |
| --- | --- | --- |
| **数学问题 · 非恒等置换单项式。** 手稿给出绝对上界 $`O(\sqrt q\log q)`$。能否对所有这类置换改进为 $`O(\sqrt q)`$？二次精确族已达到幂指数 $`1/2`$，去掉对数因子的普遍结论仍未确定。 | [上界与问题](../../VariableDegree.html#L142) | [非零斜率的像集界](../../lean/PencilCollisionCover.lean#L140) · [达到平方根阶的例子](../../lean/PhaseQuadratic.lean#L206) |
| **形式化缺口 · 非同步侧的无条件证明。** 还需在所选求和域上形式化精确阶乘法特征的一元 Weil 界。该经典定理在上面的最小值定理中作为参数传入。 | [几何非幂条件与求和域](../../VariableDegree.html#L166) | [Weil 界的签名](../../lean/PiecewiseWeil.lean#L23) · [逐项应用](../../lean/PiecewiseWeil.lean#L133) |
| **形式化缺口 · 同域的两个非单项式实例。** 在 $`q=t^6`$、$`t\equiv1\bmod 6`$ 时，手稿用同一对系数构造两个非单项式置换，阻塞数分别为 $`\Theta(t^2)`$ 和 $`\Theta(\log q)`$。Lean 已有标号置换判据和一般系数表定理；将非单项式性、两种周期情形及其最小值合写为这一实例的 Lean 陈述仍待完成。 | [具体构造](../../VariableDegree.html#L161) | [标号置换判据](../../lean/PiecewiseFrobenius.lean#L18) · [同步侧](../../lean/PiecewiseSyncUpper.lean#L165) · [非同步侧](../../lean/PiecewiseMinimum.lean#L56) |

[全仓核验状态](../../STATUS.md) · [Lean 工程索引](../../lean/README.md) · [源码哈希与公理记录](../../lean/verification.txt)

[研究时间线与关键提交](../../TIMELINE.md) · [仓库首页](../../README.md)
