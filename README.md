# 有限域上单项式曲线的竖直平移与阻塞数

对有限域 $\mathbb F_q$，记 $B(q,d)$ 为使曲线 $YZ^{d-1}=X^d-\alpha Z^d$ 的有理点并集截到每条有理射影直线所需的最少参数数目。本文研究 Asgarli、Ghioca 和 Yip 的问题 5.4。研究手稿和形式化署名 **GPT-Astra**（AI）。[中文手稿（PDF）](Manuscript.pdf) · [HTML 全文](Manuscript.html) · [原问题](https://doi.org/10.1007/s10623-026-01958-z)

## 一般次数与精确值

固定任意 $d\ge2$，沿全部素数幂 $q\to\infty$，手稿证明

$$
B(q,d)=\Theta_d(\log q),\qquad
\liminf_{q\to\infty}\frac{B(q,d)}{\log q}\ge \frac{1}{2\log(d!)}.
$$

这里的 $\log$ 为自然对数。AGY 定理 5.1 已给出一般上界，新增的下界覆盖所有坏特征。其中特征 $p$ 整除 $d$ 而 $d$ 不是 $p$ 的幂时，所有平移覆盖只有一个公共野分支点。按 Dot 提议的路线，第 11 节选择斜率使几何分裂域两两不同，证明各因子的非阿贝尔单群直积嵌入几何群，再在算术 Frobenius 陪集内安排同时错排。复合曲线的亏格至多为 $C_d\ell(d!)^\ell$，所以当 $\ell=\lfloor c\log q\rfloor$、$c<1/(2\log(d!))$ 时，Hasse–Weil 界仍给出漏线。这确定了问题 5.4 的增长阶，精确首项系数一般仍然开放。[全特征定理](Manuscript.html#all-characteristics) · [AGY，§5](https://arxiv.org/html/2510.15332v2#S5)

对 $d\ge3$ 且 $p\nmid d(d-1)$，第 7–10 节的下极限系数更大，达到 $1/[2(d-1)\log 2]$。Dot 提议在阻塞问题中选取避碰斜率。共享驯分歧点处的独立性、长轮换上的特征标估计均有先例。三次情形的对数阶还可由 Pollack 的同时不可约估计推出。[驯分歧定理](Manuscript.html#log-bound) · [Pollack 原文](https://www.pollack-math.net/twinsl.pdf)

## 次数随域阶增长

令 $\tau_q(d)$ 为 $\mathbb F_q$ 中幂值集 $\{x^d\}$ 的最少平移覆盖数，$h=\gcd(d-1,q-1)$。对每个 $d\ge2$、每个有限域，任意已有的水平覆盖都能补成射影阻塞集，并且

$$
0\le B(q,d)-\tau_q(d)\le \left\lceil\frac{2\log q}{\log(1+1/h)}\right\rceil .
$$

对范数幂可以求出精确值。令 $q=s^n$、$n\ge2$、$D=(q-1)/(s-1)$。对**每个** $m\ge1$ 有 $B(q,mD)=s^{n-1}\tau_s(m)$。特别地，$B(q,D)=s^{n-1}$，每个最优参数集产生的阻塞集均不含整条有理直线。两条定理都已在 Lean 中接到 AGY 的射影最小值定义。[手稿第 19–20 节](Manuscript.html#variable-degree) · [一般界](lean/PencilCollisionCover.lean) · [范数族总定理](lean/NormPowerMinimum.lean)

例如 $q=81=3^4$，$D=40$。在 $\mathbb F_3$ 中一次幂满射，二次幂的值集为 $\{0,1\}$，需要两个平移。因此 $B(81,40)=27$，$B(81,80)=54$。

## 扩张次数的整除二分律

固定 $m\ge2$，设 $m\mid s-1$、$q=s^n$、$n\ge1$，取 $d=s+(q-1)/m$。定理 10 给出 $m\mid n$ 时 $B(q,d)=\Theta_m(ns)$，$m\nmid n$ 时 $B(q,d)=\Theta_m(\log q)$。常数对底域和扩张次数一致。整除侧有显式下界 $1+n(s-1)/m$。非整除侧对每组至多 $\log q/(32m^2\log m)$ 个参数都能找到遗漏直线，一个统一的充分条件为 $\log q\ge16384m^5$。[定理与迹投影](Manuscript.html#extension-dichotomy) · [共同换元与字符和](Manuscript.html#phase-weil) · [退化分支](Manuscript.html#phase-independence)

取任意奇素数幂 $t$（例如 $5^k$）、$q=t^6$、$m=2$。在同一有限域上，指数 $(q-1)/2+t^3$ 与 $(q-1)/2+t^2$ 都给出置换，前者的阻塞数恰为 $\sqrt q$，后者为 $\Theta(\log q)$。两者的水平线均只需一次平移。对任意奇素数幂 $s$，二次公式 $B(s^2,s+(s^2-1)/2)=s$ 已由 Lean 无条件验证。整除侧的整条 $\Theta_m(ns)$ 双边界和非整除侧的对数上界也已无条件形式化。非整除侧对数下界中的逐项 Weil 界及其完整应用仍见手稿。[同域对照](Manuscript.html#phase-exact) · [二次射影最小值](lean/PhaseQuadratic.lean) · [形式化范围](lean/README.md#扩张次数的整除二分律)

## 固定次数的上界系数

令 $L=\log q$、$r=\gcd(d,q-1)$。当 $p\nmid d(d-1)$ 时，令 $\delta_d$ 为 $S_d$ 中错排的比例，$\lambda=\log(1/\delta_d)$。若 $r>1$，再令 $\mu=\log(r/(r-1))$。分斜率取样配合一次共同补点给出
$$
B(q,d)\le\max\!\left\{\frac{2L-\log L}{\lambda},\,\frac{L-\log L}{\mu}\right\}+O_d(1).
$$
$r=1$ 时只取第一项。此时固定次数的上界系数 $2/\lambda$ 随 $d\to\infty$ 趋于 2。在 $p\nmid d$ 且 $p\mid d-1$ 时上式可取 $\lambda=\log 2$。Lean 无条件核验了水平遗漏数、分组取样和错排系数的极限。几何估计在形式陈述中保留为前提，详见索引。[手稿第 21 节](Manuscript.html#split-upper) · [Lean 核验范围](lean/README.md#变次数和分斜率上界)

## 三次置换族

对特征 $p>3$ 且 $q\equiv2\pmod 3$ 的所有充分大的素数幂，令 $L=\log q$。第 12–17 节给出

$$
\frac{L-2\log L}{\log 4}-5 < B(q,3)
\le \frac{2L-\log L}{\log 3}+17.
$$

因此 $B(q,3)/\log q$ 的下极限至少为 $1/\log 4$，上极限至多为 $2/\log 3$。固定斜率给出的下极限是 $1/\log16$。真实首项系数、上下极限是否相同以及真实次项仍然开放。特征 2 的 $q=2^{2h+1}$ 由第 18 节单独处理，目前的下极限估计为 $1/\log16$。[两参数定理](Manuscript.html#cubic-two-parameters) · [特征 2](Manuscript.html#cubic-char2)

对每个 $\ell$ 元参数集，换元将遗漏直线转成穿孔直线上有序点对的计数。乘以 $3^\ell$ 后主项为 $(q-\ell)(q-\ell-1)$。系数表示取自 $S_3^\ell$，非平凡项的总秩为 $4^\ell-1$，一阶上同调维数总和至多 $10\ell\,2^\ell$。二者分别控制 $q$ 与 $q^{3/2}$ 量级的误差。只要有一个符号因子，余循环就由单个向量决定。这个限制给出对增长的 $\ell$ 一致的次阶下界。[余循环维数证明](Manuscript.html#cubic-cocycles) · [正特征比较](Manuscript.html#cubic-comparison) · [误差汇总与优先权](Manuscript.html#cubic-leading-term)

## 有限域上的精确结果

| 域与次数 | 最小值与最优参数集 |
| --- | --- |
| $q=p^h,\ d=p^e,\ g=\gcd(h,e)$ | $1+(h/g)(p^g-1)$。若 $h\mid e$，只有全域能阻塞，曲线并含整条直线。若 $h\nmid e$，最优解均非平凡。 |
| $q=8,\ d=2$ | 最小值 4，恰有 56 个最优参数集。 |
| $q=32,\ d=6$ | 最小值 7。10,912 个最优参数集在 $\mathrm{AGL}_1(32)$ 下分成 11 个轨道，每个轨道有 992 个集合。 |
| $q=41,\ d=3$ | 最小值 5。五次单位根集合的仿射轨道给出全部 328 个最优解。 |
| $q=47,\ d=3$ | 最小值 5。Dot 给出的 $\{0,1,3,15,33\}$ 有平凡稳定子，其轨道给出全部 2,162 个最优解。 |

Dot 给出了 $q=32$ 的最小值与轨道数。这里每条非水平线对应的可选参数构成 $\operatorname{Im}(x^6+x)$ 的一个仿射像。这些区组已由 Ding 和 Tang 识别为一个 $3$-$(32,16,112)$ 设计，故 $B(32,6)$ 也是该设计的最小横截集基数。进一步允许 Frobenius 平方自同构后，这 11 个轨道在 $\mathrm{A\Gamma L}_1(32)$ 下合并为三个，大小为 992、4,960、4,960。第 5.1 节给出独立复算的方法。[六次算例](Manuscript.html#sextic32) · [Ding–Tang，推论 30](https://cse.hkust.edu.hk/faculty/cding/JOURNALS/amc211.pdf#page=14)

## 证明与复现

Lean 4.8.0 核验了表中的最小值，以及 $q=8,41,47$ 的最优解计数。对于 $q=32$，两套 Python 穷举分别从直线方程和参数值集重建七元解，并比较完整轨道。只导入 mathlib 的陈述文件直接定义射影点、射影直线、几何不可约曲线族和问题 5.4 的最小值，与主库谓词的等价性已形式化。[独立陈述](lean/ProblemStatement.lean) · [定理与证明索引](lean/README.md) · [32 元域分类](checks/sextic32.py)

| 渐近结论 | Lean 已核验的范围 |
| --- | --- |
| 三次上界，无条件 | 对任意 $q\equiv2\pmod3$，每条仿射直线漏掉的参数数目 $M$ 满足 $3M\le q+1$。对 $q\ge16$，独立射影陈述中的最小值满足 $B(q,3)\le2\log q/\log3+8$，包括特征 2。[像集计数](lean/CubicValueSet.lean) · [最小值定理](lean/CubicCovering.lean) |
| 第 17 节，亏格与有理位，无条件 | 对实际 Laurent 分支 $K/\mathbb F_q(t)$，基域和每个单根子域的全局正则微分空间均为零。在参数直线的每个有理点（含无穷远点）上，纤维中的有理位个数至多为 $[K:\mathbb F_q(t)]$。因此 $K$ 的全部有理位构成有限集，其基数至多为 $(q+1)[K:\mathbb F_q(t)]$。[有理域微分](lean/CubicRationalGenus.lean) · [极点纤维](lean/CubicPoleDegree.lean) · [全部有理位](lean/CubicFiniteFibres.lean) |
| 第 17–18 节，含负 $\log\log q$ 项的上界 | 对 $q\equiv2\pmod3$（包括特征 2），$L=\log q\le3^9$ 时，Lean 无条件证明 $B(q,3)\le(2L-\log L)/\log3+17$。对任意大小的 $q$，Lean 已证明由 Castelnuovo–Severi 亏格界和 Hasse–Weil 有理点下界推出同一结论。两项几何输入只用于至少三条残余线且满足严格点数阈值的情形。[射影最小值](lean/CubicLogLog.lean) · [已证步骤与待接入的定理](lean/README.md#第-17-节的函数域输入) |
| 三次下界，依赖几何输入 | 从实际有理根数展开特征标，按张量类型证明维数界并求和。给定相应覆盖的局部惯性、迹公式、对偶及逐特征值权界等输入，Lean 推出奇特征的 $1/\log4$ 和特征 2 的 $1/\log16$。两式的总误差都在库内导出。[曲面](lean/CubicSurfaceTrace.lean) · [曲线](lean/CubicCurveTrace.lean) |
| 纸面结果 | 全特征一般次数定理中的几何群分类、亏格估计及扭曲下降见手稿。[逐项验证范围](lean/README.md) · [公理与源码记录](lean/verification.txt) |

首次在仓库根目录复现时运行

~~~sh
(cd lean && lake exe cache get)
python3 checks/verify_lean.py --serial
~~~

GitHub Actions 直接运行上述验证程序（其中包含 `lake build`），随后用 Python 标准库运行七项独立检查。模 47 的枚举固定一个参数，Lean 证书固定两个参数。两条路径分别给出 230 个含 0 的五元解和 20 个含 0、1 的五元解。矩阵程序检查 $\ell\le6$ 的全部 83 种张量类型。[验证工作流](.github/workflows/verify.yml) · [模 47 枚举](checks/cubic47.py) · [固定斜率](checks/cubic_slope.py) · [两参数与逐线计数](checks/cubic_pairs.py) · [上同调矩阵](checks/cubic_cohomology.py) · [二次范数的 26,960 组交叉核对](checks/norm_quadratic.py)

第 22 节的独立程序重建有限域与直线方程。在 27 元域遍历全部非零斜率、平移与换元参数，核对 18,954 组候选原像。125 元域的合数指标 $m=4$ 给出另 62,500 组纤维检查，覆盖全部四个斜率范数。在同一 15,625 元域，直接检查二次构造覆盖全部斜率，并检查三次扩张中每个非零斜率轨道的像集。[二分律的有限核对](checks/phase_dichotomy.py)

## 彩蛋

[RMM 2026 六题中文答卷（PDF）](bonus/RMM-2026-中文答卷.pdf) · [HTML 与原题链接](bonus/RMM-2026-中文答卷.html)
