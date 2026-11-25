# 有限域上单项式曲线的竖直平移与阻塞数

对有限域 $\mathbb F_q$，记 $B(q,d)$ 为使曲线 $YZ^{d-1}=X^d-\alpha Z^d$ 的有理点并集截到每条有理射影直线所需的最少参数数目。本文研究 Asgarli、Ghioca 和 Yip 的问题 5.4。研究手稿和形式化署名 **GPT-Astra**（AI）。[中文手稿（PDF）](Manuscript.pdf) · [HTML 全文](Manuscript.html) · [原问题](https://doi.org/10.1007/s10623-026-01958-z)

## 三次置换族

对特征 $p>3$ 且 $q\equiv2\pmod 3$ 的所有充分大的素数幂，令 $L=\log q$。第 12–17 节给出

$$
\frac{L-2\log L}{\log 4}-5 < B(q,3)
\le \frac{2L-\log L}{\log 3}+O(1).
$$

因此 $B(q,3)/\log q$ 的下极限至少为 $1/\log 4$，上极限至多为 $2/\log 3$。固定斜率给出的下极限是 $1/\log16$。真实首项系数、上下极限是否相同以及真实次项仍然开放。特征 2 的 $q=2^{2h+1}$ 由第 18 节单独处理，目前的下极限估计为 $1/\log16$。[两参数定理](Manuscript.html#cubic-two-parameters) · [特征 2](Manuscript.html#cubic-char2)

对每个 $\ell$ 元参数集，换元将遗漏直线转成穿孔直线上有序点对的计数。乘以 $3^\ell$ 后主项为 $(q-\ell)(q-\ell-1)$。系数表示取自 $S_3^\ell$，非平凡项的总秩为 $4^\ell-1$，一阶上同调维数总和至多 $10\ell\,2^\ell$。二者分别控制 $q$ 与 $q^{3/2}$ 量级的误差。只要有一个符号因子，余循环就由单个向量决定。这个限制给出对增长的 $\ell$ 一致的次阶下界。[余循环维数证明](Manuscript.html#cubic-cocycles) · [正特征比较](Manuscript.html#cubic-comparison) · [误差汇总与优先权](Manuscript.html#cubic-leading-term)

## 一般次数与精确值

固定 $d\ge3$，若 $p\nmid d(d-1)$，则 $B(q,d)=\Theta_d(\log q)$，下极限系数至少为 $1/[2(d-1)\log 2]$。Dot 提议在阻塞问题中选取避碰斜率。共享驯分歧点处的独立性、长轮换上的特征标估计均有先例。三次对数阶还可由 Pollack 的同时不可约估计直接推出，见第 10 节对常数的换算。[一般定理](Manuscript.html#log-bound) · [Pollack 原文](https://www.pollack-math.net/twinsl.pdf)

| 域与次数 | 最小值与最优参数集 |
| --- | --- |
| $q=p^h,\ d=p^e,\ g=\gcd(h,e)$ | $1+(h/g)(p^g-1)$。若 $h\mid e$，只有全域能阻塞，曲线并含整条直线。若 $h\nmid e$，最优解均非平凡。 |
| $q=8,\ d=2$ | 最小值 4，恰有 56 个最优参数集。 |
| $q=41,\ d=3$ | 最小值 5。五次单位根集合的仿射轨道给出全部 328 个最优解。 |
| $q=47,\ d=3$ | 最小值 5。Dot 给出的 $\{0,1,3,15,33\}$ 有平凡稳定子，其轨道给出全部 2,162 个最优解。 |

## 证明与复现

Lean 4.8.0 和锁定的 mathlib 核验了上表、几何不可约性、scattered 映射刻画及三次避碰斜率引理。第 14–16 节的上同调、正特征转移和渐近不等式采用纸面证明。原文公式 (5.4) 有一份只导入 mathlib 的独立陈述，与射影谓词的等价性已在 Lean 中证明。该对照由本仓库维护。[形式陈述与代码索引](lean/README.md) · [当前源码验证记录](lean/verification.txt)

首次在仓库根目录复现时运行

~~~sh
(cd lean && lake exe cache get)
python checks/verify_lean.py
~~~

四个独立检查均使用 Python 标准库。模 47 的枚举固定一个参数，Lean 证书固定两个参数；两条路径分别给出 230 个含 0 的五元解和 20 个含 0、1 的五元解。矩阵程序检查 $\ell\le6$ 的全部 83 种张量类型。[模 47 枚举](checks/cubic47.py) · [固定斜率](checks/cubic_slope.py) · [两参数与逐线计数](checks/cubic_pairs.py) · [上同调矩阵](checks/cubic_cohomology.py)

## 彩蛋

[RMM 2026 六题中文答卷（PDF）](bonus/RMM-2026-中文答卷.pdf) · [HTML 与原题链接](bonus/RMM-2026-中文答卷.html)
