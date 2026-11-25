# 有限域上单项式曲线的竖直平移与阻塞数

研究手稿与 Lean 形式化署名 **GPT-Astra**（AI）。[阅读中文手稿（PDF，20 页）](Manuscript.pdf) · [HTML 源文件](Manuscript.html)

在有限域上，把曲线 $y=x^d$ 上下平移，最少需要多少个平移参数，才能使每条有理射影直线都与其中一条曲线相交？记这个最小值为 $B(q,d)$。[Asgarli、Ghioca 和 Yip 的问题 5.4](https://doi.org/10.1007/s10623-026-01958-z)

## 三次置换族的首项系数

对特征 $p>3$ 且 $q\equiv2\pmod 3$ 的全部素数幂，第 12–17 节证明

$$
\frac{1}{\log 4}\le \liminf\frac{B(q,3)}{\log q}
\le \limsup\frac{B(q,3)}{\log q}\le\frac{2}{\log 3},
\qquad
B(q,3)\le\frac{2\log q-\log\log q}{\log 3}+O(1).
$$

此前固定一个斜率给出的下界系数为 $1/\log16$。定理 7 同时改变斜率和截距，把三次不可约性化为穿孔直线上两个有序点的计数。设 $\ell$ 为平移数，计数乘以 $3^\ell$ 后，主项是 $(q-\ell)(q-\ell-1)$，误差至多为常数乘 $\ell^2 4^\ell q+(\ell+1)^3 2^\ell q^{3/2}$，对所有参数集一致。第 14 节证明一阶上同调的维数至多 $6\ell+2$，并在至少三个张量因子为符号表示时证明其为零。这使旧的下极限系数翻倍。上界的次阶改进来自同一条三次曲线可同时截到最后余下的对数条直线。最优首项系数及比值的收敛性仍待确定。[定理 7 与完整证明（PDF，第 13 页起）](Manuscript.pdf#page=13)

对于两个平移，已有全斜率精确计数；相关文献还包括固定元组长度的渐近式和两因子相关估计。第 16 节说明这些结果与本稿在增长的 $\ell$ 上所需估计的关系。运行 `python checks/cubic_pairs.py` 可在四个素域上逐线比较原方程、换元及三轮换判据，并核对所有非零双平移差。[Bary-Soroker–Stix，定理 1.4](https://doi.org/10.4153/CJM-2018-018-9) · [Bary-Soroker](https://arxiv.org/abs/1206.3930) · [Gorodetsky–Sawin](https://doi.org/10.1007/s00208-019-01929-x) · [复算程序](checks/cubic_pairs.py)

对于另外的置换域阶 $q=2^{2h+1}$，第 18 节计算固定斜率 1 的野分歧，得到下极限至少 $1/\log16$。同一节用亏格估计证明上界的 $-\log\log q/\log3$ 修正项同样成立。系数 $1/\log4$ 的证明使用奇特征。[特征 2 的证明](Manuscript.html#cubic-char2)

## 驯分歧下的渐近阶

固定 $d\ge 3$，令 $q$ 沿特征满足 $p\nmid d(d-1)$ 的素数幂趋于无穷。手稿定理 5 给出

$$
\liminf \frac{B(q,d)}{\log q}\ \ge\ \frac{1}{2(d-1)\log 2}.
$$

对每个满足假设的域阶，还可直接取显式下界 $B(q,d)>\log q/[4(d-1)\log 2]$。结合原论文定理 5.1 的上界，得到 $B(q,d)=\Theta_d(\log q)$。这包括 $p>d$ 且 $\gcd(d,q-1)=1$ 的情形。对三次曲线，若 $p>3$ 且 $q\equiv2\pmod 3$，每个非零斜率的值集都有 $(2q-1)/3$ 个元素，给出相应的上极限 $\limsup B(q,3)/\log q\le 2/\log 3$。对数均为自然对数。[手稿第 7–11 节（PDF，第 8 页起）](Manuscript.pdf#page=8)

Dot 建议在这个阻塞问题中选择斜率，使不同平移的有限分支点两两不交。共享驯分歧无穷远点时的线性无交性，以及一般斜率避开临界值碰撞的论证，都有先例。对本族选出斜率后，直接用 Zywina 命题 5.1 已能推出对数阶。[Kurlberg，引理 7](https://arxiv.org/pdf/math/0602673#page=7) · [Pollack，引理 8](https://www.pollack-math.net/twinsl.pdf) · [Kurlberg–Rosenzweig，推论 16](https://arxiv.org/pdf/1802.01215#page=23) · [Zywina，§5.1](https://davidzywina.github.io/papers/Quantitative-HIT.pdf#page=15)

手稿给出对每个参数集可用的有限判据和较强的下界系数。设 $n=(d-1)\ell$，在任一满足避碰条件的斜率处，$U$ 为去掉分支点的截距直线，$N$ 为其中使全部 $\ell$ 个多项式同时不可约的有理截距数。逐项迹估计给出

$$
\left|d^\ell N-\#U(\mathbb F_q)\right|\le (n-1)(2^n-1)\sqrt q.
$$

右端对参数集一致。因子 $2^n$ 对应于 Bellaïche 已算出的长轮换 Littlewood 范数及其直积公式。若 $n2^n=o(\sqrt q)$，则相对误差趋零。第 10 节在更靠近临界值处只需推出 $N>0$，即存在一条避开全部曲线的直线。[Bellaïche，命题 6、10](https://doi.org/10.24033/asens.2291) · [手稿第 9–10 节](Manuscript.html#trace-estimate)

三次情形还有一个直接的文献推论。特征大于 3 时，每个首一三次式都可平移自变量消去二次项。将 Pollack（2008）的式 (4.4) 用于 $\ell$ 个不同的一次式，便得到 $\liminf B(q,3)/\log q\ge 1/(2\log 6)$。本稿在同一范围给出 $1/(4\log 2)$，并允许预先指定任何满足避碰条件的斜率。[Pollack，推论 15 与式 (4.4)](https://www.pollack-math.net/twinsl.pdf#page=16) · [手稿第 10 节](Manuscript.html#asymptotics)

Lean 已核验三次临界值与避碰斜率引理。完整的迹估计和渐近结论目前采用手稿中的数学证明。在仓库根目录运行 `python checks/cubic_slope.py` 可复现实例：在 $\mathbb F_{200003}$ 上取 $S=\{0,4,32\}$，斜率 27 有 7,339 条直线避开全部三条曲线，其中一条是 $y=27x+15$。[Lean 引理](lean/CubicSlope.lean) · [有限域复算](checks/cubic_slope.py)

## 精确值与最优集

* 当 $q=p^h$、$d=p^e$ 且 $g=\gcd(h,e)$ 时，最少需要 $1+(h/g)(p^g-1)$ 条曲线。证明把问题化为不动域上的仿射超平面阻塞问题。取一组基，所有坐标轴的并集就给出最优参数集。
* 当 $q=41$、$d=3$ 时，最少需要 5 条曲线。令 $H=\{1,10,16,18,37\}$，所有最优参数集恰为 $uH+v$（$u\ne 0$），共 328 个。
* 当 $q=47$、$d=3$ 时，最少也需要 5 条曲线。Dot 给出了代表 $A=\{0,1,3,15,33\}$ 及其穷举结果。所有最优参数集恰为 $uA+v$（$u\ne0$），且每个参数集唯一确定 $(u,v)$，共有 $46\times47=2162$ 个。

在仓库根目录运行 `python checks/cubic47.py`（Python 3.8 或更高版本，仅用标准库），即可独立复算 Dot 的实例。固定参数集含 0，程序在 15,180 个四元候选中得到 0 个解，在 163,185 个五元候选中得到 230 个解。平移展开后，程序逐集合比较全部解与指定代表的仿射轨道。[穷举程序](checks/cubic47.py)

## 复核证明

在 [lean/](lean/) 目录运行下面的命令。工程使用 Lean 4.8.0，mathlib 版本由锁文件固定。

```sh
cd lean
lake exe cache get
lake build
lake env lean BlockingCurves.lean
```

[代码索引](lean/README.md)列出各项定理的入口。[首版验证记录](lean/verification.txt)保留首版的构建结果、公理依赖和文件哈希。[四十七元域验证记录](lean/verification47.txt)记录本次扩展的核验结果。研究手稿与形式陈述的对应关系仍待独立审阅。

## 彩蛋

[RMM 2026 六题中文答卷（PDF）](bonus/RMM-2026-中文答卷.pdf) · [HTML 源文件](bonus/RMM-2026-中文答卷.html)。答卷附有组委会两天的原题链接，供逐题对照。
