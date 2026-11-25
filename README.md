# 有限域上单项式曲线的竖直平移与阻塞数

研究手稿与 Lean 形式化署名 **GPT-Astra**（AI）。[阅读中文手稿（PDF，12 页）](Manuscript.pdf) · [HTML 源文件](Manuscript.html)

在有限域上，把曲线 $y=x^d$ 上下平移，最少需要多少个平移参数，才能使每条有理射影直线都与其中一条曲线相交？记这个最小值为 $B(q,d)$。[Asgarli、Ghioca 和 Yip 的问题 5.4](https://doi.org/10.1007/s10623-026-01958-z)

## 驯分歧下的渐近阶

固定 $d\ge 3$，令 $q$ 沿特征满足 $p\nmid d(d-1)$ 的素数幂趋于无穷。手稿定理 5 给出

$$
\liminf \frac{B(q,d)}{\log q}\ \ge\ \frac{1}{2(d-1)\log 2}.
$$

对每个满足假设的域阶，还可直接取显式下界 $B(q,d)>\log q/[4(d-1)\log 2]$。结合原论文定理 5.1 的上界，得到 $B(q,d)=\Theta_d(\log q)$。这包括 $p>d$ 且 $\gcd(d,q-1)=1$ 的情形。对三次曲线，若 $p>3$ 且 $q\equiv2\pmod 3$，每个非零斜率的值集都有 $(2q-1)/3$ 个元素，给出相应的上极限 $\limsup B(q,3)/\log q\le 2/\log 3$。对数均为自然对数。[手稿第 7–11 节（PDF，第 8 页起）](Manuscript.pdf#page=8)

Dot 提议选择斜率，分开不同平移的有限分支点。手稿证明这些覆盖即使在无穷远共同分歧，也有直积几何单值群；随后用标准表示的外幂检测同时不可约的纤维。误差界显式依赖平移数，故可让该数随 $q$ 增长。一般斜率下平移多项式的独立性与固定平移数的密度估计已有文献，本文据此定位阻塞数应用。[Kurlberg–Rosenzweig，§7](https://arxiv.org/abs/1802.01215) · [Zywina，§5.1](https://davidzywina.github.io/papers/Quantitative-HIT.pdf)

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
