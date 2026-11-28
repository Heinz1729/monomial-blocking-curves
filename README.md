# 有限域上单项式曲线的竖直平移与阻塞数

在 $`\mathbb{F}_q`$ 上，$`B(q,d)`$ 是使曲线 $`YZ^{d-1}=X^d-\alpha Z^d`$ 的有理点并集遇到每条有理射影直线所需的最少参数数目。两篇手稿分别研究固定次数和随域阶变化的次数，共用一套射影问题陈述与可执行证书。署名 GPT-Astra（AI）。[AGY 问题 5.4](https://arxiv.org/html/2510.15332v2#S5) · [独立形式陈述](lean/ProblemStatement.lean)

| 手稿 | 主要问题 | 全文 |
| --- | --- | --- |
| **I　单项式曲线竖直平移的阻塞数：固定次数的对数界** | 固定 $`d`$、令 $`q`$ 增长时的对数阶，以及三次置换族的上下界 | [排版 PDF](Manuscript.pdf) · [HTML 源码](Manuscript.html) |
| **II　变次数单项式曲线的阻塞数：范数幂与扩张次数的整除律** | 同一有限域上哪些次数有可精确计算的最小值，何时出现不同增长阶 | [排版 PDF](VariableDegree.pdf) · [HTML 源码](VariableDegree.html) |

可在 GitHub 直接阅读排版 PDF。下文的章节链接指向 HTML 源码，下载对应文件并用浏览器打开即可阅读公式和使用文内目录。

第一篇英文预印本以图像族和尖点族为主线，给出固定次数的全特征对数阶、三次置换的 $`1/\log 4`$ 下界，以及同域同次数下 $`3`$ 对 $`2s-1`$、$`4`$ 对 $`3s-2`$ 的精确比较。英文署名为 GPT-6.2 Astra（AI）。[英文论文](papers/FixedDegreePencils.pdf) · [LaTeX 源码](papers/FixedDegreePencils.tex) · [投稿要点](papers/FixedDegreePencils-highlights.txt)

定理 6 的英文独立稿集中讨论分段 Frobenius 图像的系数周期、同步斜率和随平移数增长的误差。可直接阅读 PDF，或由同目录的单文件 LaTeX 源码复现。中文第二篇保留范数幂等完整结果。[英文论文](papers/CoefficientPeriods.pdf) · [LaTeX 源码](papers/CoefficientPeriods.tex) · [投稿用研究要点](papers/CoefficientPeriods-highlights.txt)

## 一般次数与精确值

第一篇给出固定 $`d\ge2`$ 时所有特征上的 $`B(q,d)=\Theta_d(\log q)`$。AGY 已证明一般上界。下界的难点出现在只有一个公共野分支点时。此时在几何群中构造单群基座的直积，在指定的算术 Frobenius 陪集中同时实现错排，再用扭曲的有理点得到漏线。修订后的逐根亏格估计为 $`2g_\ell\le\ell(d-1)\lvert H\rvert`$，其中 $`H`$ 为几何复合群。得出的下极限系数至少为 $`1/(2\log(d!))`$。这部分的实际覆盖、亏格及扭曲属于纸面证明。[第一篇定理 2](Manuscript.html#all-characteristics) · [证明复核记录](REVIEW.md)

令 $`L=\log q`$。在 $`p\gt 3`$、$`q\equiv2\pmod{3}`$ 的三次置换族，第一篇给出的充分大域阶上的界为

```math
\frac{L-2\log L}{\log 4}-5\lt B(q,3)\le\frac{2L-\log L}{\log 3}+17.
```

奇特征的 $`1/\log 4`$ 使用两参数曲面的迹估计。特征 2 的置换族由固定斜率的一维野导子估计给出 $`1/\log 16`$。两条下界所需的几何输入不同。三次情形的真正首项常数仍待确定。[第一篇定理 3](Manuscript.html#cubic-two-parameters) · [特征 2](Manuscript.html#cubic-char2) · [固定次数的分斜率上界](Manuscript.html#split-upper)

对有限尖点的三次族 $`(Y+\alpha Z)^2 Z=X^3`$，第一篇定理 4 将全部射影漏线与原曲面上的有序配置逐一对应。误差对 $`\ell\le c\log q`$、$`c\lt 1/\log 4`$ 保持一致。十一元域中，尖点族只需 3 个平移，原图像族需要 4 个。[尖点族与仿射图样](Manuscript.html#cuspidal-translates) · [Lean 计数恒等式](lean/CuspidalTransfer.lean)

## 次数随域阶增长

设 $`\tau_s(m)`$ 为 $`\mathbb{F}_s`$ 中 $`m`$ 次幂值集的最少平移覆盖数。当 $`q=s^n`$、$`n\ge2`$、$`D=(q-1)/(s-1)`$ 时，有精确公式 $`B(q,mD)=s^{n-1}\tau_s(m)`$。特别地，$`B(q,D)=s^{n-1}`$。对于任意次数，第二篇还用 $`h=\gcd(d-1,q-1)`$ 控制从水平覆盖扩充到射影阻塞集所需的额外参数数目。[第二篇定理 3](VariableDegree.html#variable-degree) · [第二篇定理 4](VariableDegree.html#norm-family)

## 扩张次数的整除二分律

固定 $`m\ge2`$，设 $`m\mid s-1`$、$`q=s^n`$、$`d=s+(q-1)/m`$。当 $`m\mid n`$ 时 $`B(q,d)=\Theta_m(ns)`$，当 $`m\nmid n`$ 时 $`B(q,d)=\Theta_m(\log q)`$。在同一个 $`q=t^6`$ 上，对任一奇素数幂 $`t`$，指数 $`(q-1)/2+t^3`$ 的阻塞数恰为 $`\sqrt q`$，指数 $`(q-1)/2+t^2`$ 的阻塞数为对数阶，两者都是置换。非整除侧下界的完整字符和证明见正文。[第二篇定理 5](VariableDegree.html#extension-dichotomy) · [字符和与退化原像](VariableDegree.html#phase-weil) · [精确值与同域对照](VariableDegree.html#phase-exact)

## 分段线性置换的系数判据

第二篇定理 6 允许不同乘法陪集使用同一底域系数。在 $`\mathbb{F}_{s^n}`$ 的 $`m`$ 个非零标号陪集上分别取 $`f(x)=c_jx^s`$，设至少有两个不同的非零系数。令 $`h`$ 为全部系数比生成的子群阶。若 $`h\mid n`$，则 $`B(f)=\Theta_m(ns)`$；若 $`h\nmid n`$，则 $`B(f)=\Theta_m(\log q)`$。常数对系数表一致。仅用平方类和非平方类两个分支即可实现任意周期 $`h\ge3`$。当 $`q=t^6`$、$`t\equiv1\bmod 6`$ 时，三阶系数产生阻塞数分别为 $`\Theta(t^2)`$ 与 $`\Theta(\log q)`$ 的两种非单项式置换。[系数周期与证明](VariableDegree.html#coefficient-period) · [重复标号与例子](VariableDegree.html#coefficient-escape)

## 证明审阅与复现

| 结论 | 当前可核验的范围 |
| --- | --- |
| 全特征对数下界 | 纸面证明。Lean 已证抽象二重传递陪集的错排存在性和数值阈值。 |
| 三次下界 $`1/\log 4`$、$`1/\log 16`$ | Lean 从实际计数与明确的几何前提推出数值下界。具体覆盖上的正特征比较、迹与权、野导子的实现见第一篇。 |
| 三次上界 | $`q\equiv2\bmod 3,\ q\ge16`$ 时的 $`2L/\log 3+8`$ 为无条件 Lean 结论。带 $`-\log L`$ 的上界在 $`L\le3^9`$ 时也已无条件形式化，全域版本接收所选根域的 Castelnuovo–Severi 与 Hasse–Weil 输入。 |
| 范数幂与分圆 Frobenius 族 | 整个范数幂公式、整除侧双边界、非整除侧上界和二次精确值均有无条件 Lean 定理。单项式的非整除侧下界见正文 §6。§7 的系数表形式化在一元乘法字符 Weil 界下证得一般分段图的最小值下界。 |
| 有限尖点三次族 | Lean 无条件证明漏线与有序对的计数恒等式。渐近下界沿用原曲面的几何输入。十一元域的两个最小值有独立穷举。 |
| 一般分段 Frobenius 系数表 | 整除侧匹配上下界和非整除侧上界均已无条件接到实际最小值。非整除侧下界的唯一外部数学输入是一元乘法字符 Weil 界。重复系数、奇异分支的全部原像、几何非幂性、范数切片和一致对数误差已由内核核验。[定理 6 的形式陈述](lean/PiecewiseMinimum.lean) |

审阅说明逐行对应了 71 行的三次计数模块，并列明有限分支、无穷远分支、常数域、扭曲和误差对 $`\ell`$ 依赖的检查位置。两篇稿件尚待独立人类专家审阅。[审阅说明](REVIEW.md) · [Lean 定理与前提索引](lean/README.md) · [公理与源码哈希](lean/verification.txt)

四组小域证书集中在计算附录。Lean 证明 $`B(8,2)=4`$、$`B(32,6)=7`$、$`B(41,3)=B(47,3)=5`$，并给出 8、41、47 元域上的最优解数 56、328、2,162。32 元域的 10,912 个最优解与 11 个仿射轨道由两套 Python 穷举交叉核对。[有限证书与复算（PDF 阅读）](FiniteCertificates.pdf) · [HTML 源码](FiniteCertificates.html) · [32 元域程序](checks/sextic32.py)

在仓库根目录运行

~~~sh
(cd lean && lake exe cache get)
python3 checks/verify_lean.py --serial
~~~

GitHub Actions 使用运行器默认栈执行串行构建和公理审计，再运行八项独立有限检查。允许的公理为 `Classical.choice`、`Quot.sound`、`propext`。[工作流](.github/workflows/verify.yml) · [验证器](checks/verify_lean.py) · [最近运行](https://github.com/Heinz1729/monomial-blocking-curves/actions/workflows/verify.yml)

原合订稿的 §7–18、§21 对应第一篇 §2–13、§14，§19–20、§22 对应第二篇 §4–6。旧记录和讨论可按提交定位。[原合订稿](https://github.com/Heinz1729/monomial-blocking-curves/blob/75326b5091df2a99b4c9e0354d1e7292ee5d61bb/Manuscript.pdf) · [RMM 2026 中文答卷](bonus/RMM-2026-中文答卷.pdf)
