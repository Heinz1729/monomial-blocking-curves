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

## 三次置换族

对特征 $p>3$ 且 $q\equiv2\pmod 3$ 的所有充分大的素数幂，令 $L=\log q$。第 12–17 节给出

$$
\frac{L-2\log L}{\log 4}-5 < B(q,3)
\le \frac{2L-\log L}{\log 3}+O(1).
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
| 三次下界，依赖几何输入 | 从实际有理根数展开特征标，按张量类型证明维数界并求和。给定相应覆盖的局部惯性、迹公式、对偶及逐特征值权界等输入，Lean 推出奇特征的 $1/\log4$ 和特征 2 的 $1/\log16$。两式的总误差都在库内导出。[曲面](lean/CubicSurfaceTrace.lean) · [曲线](lean/CubicCurveTrace.lean) |
| 纸面结果 | 全特征一般次数定理的几何证明与第 17 节上界的 $-\log\log q/\log3$ 修正见手稿。[逐项验证范围](lean/README.md) · [公理与源码记录](lean/verification.txt) |

首次在仓库根目录复现时运行

~~~sh
(cd lean && lake exe cache get)
python3 checks/verify_lean.py --serial
~~~

GitHub Actions 直接运行上述验证程序（其中包含 `lake build`），随后用 Python 标准库运行五项独立检查。模 47 的枚举固定一个参数，Lean 证书固定两个参数。两条路径分别给出 230 个含 0 的五元解和 20 个含 0、1 的五元解。矩阵程序检查 $\ell\le6$ 的全部 83 种张量类型。[验证工作流](.github/workflows/verify.yml) · [模 47 枚举](checks/cubic47.py) · [固定斜率](checks/cubic_slope.py) · [两参数与逐线计数](checks/cubic_pairs.py) · [上同调矩阵](checks/cubic_cohomology.py)

## 彩蛋

[RMM 2026 六题中文答卷（PDF）](bonus/RMM-2026-中文答卷.pdf) · [HTML 与原题链接](bonus/RMM-2026-中文答卷.html)
