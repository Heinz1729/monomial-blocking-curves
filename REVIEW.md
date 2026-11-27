# 算术几何审阅说明

两篇手稿共用一套射影问题陈述和 Lean 工程。本文记录仓库内的逐段复核，并给出可独立检验的重要推理。尚无外部有限域算术几何或有限几何专家逐行审阅并签署的记录。以下「基线」链接固定在提交 `75326b5`，用于逐行比较。本说明沿用基线节号。基线 §§7–18 对应修订后第一篇 §§2–13，基线 §22 对应第二篇 §6。[独立问题陈述](lean/ProblemStatement.lean) · [逐定理形式化范围](lean/README.md) · [AGY 问题 5.4](https://arxiv.org/html/2510.15332v2#S5)

## 固定次数的下界

**§§7–10，有限分支不交。** 设 $d\ge3$ 且 $p\nmid d(d-1)$。给定任意大小为 $\ell$ 的平移集，在几何域中分开所有有限临界值。设 $N=(d-1)\ell$，共用的无穷远点仍为驯分歧。新分裂域与此前各域的复合取交，商覆盖仅可能在无穷远驯分歧，Riemann–Hurwitz 排除其次数大于一。由此先得几何群 $S_d^\ell$，再由算术群在同一乘积内的忠实作用推出常数域为 $\mathbb F_q$。

这里允许 $p\mid d!$，需要逐点核对伽罗瓦闭包的驯性。逐特征标的导子计算给出 $(N-1)(2^N-1)\sqrt q$ 的误差，直接保留了对变化的 $\ell$ 的依赖。驯三次的 $1/\log16$ 可由既有逐特征标估计与全轮换指示函数的 Littlewood 范数推出。[基线 113–158 行](https://github.com/Heinz1729/monomial-blocking-curves/blob/75326b5091df2a99b4c9e0354d1e7292ee5d61bb/Manuscript.html#L113-L158) · [固定次数稿 §3](Manuscript.html#monodromy) · [Zywina，命题 5.1](https://davidzywina.github.io/papers/Quantitative-HIT.pdf) · [Bellaïche，命题 6、10](https://doi.org/10.24033/asens.2291)

**§11，仅有共同野分支点。** 当 $p\mid d$ 且 $d$ 非 $p$ 幂，几何分裂域都只在无穷远分歧。斜率避开有限个平移对称后得到两两不同的分裂域。检查 Goursat 引理给出的两坐标图像及各坐标核的固定域，得出几何群含有 $T^\ell$，其中 $T$ 是非阿贝尔单基座。

28 点例外产生三阶商，而 $p=2$ 或 $7$，这个几何商至多在无穷远驯分歧，仍由 Riemann–Hurwitz 排除。几何群含有该直积仍允许各坐标共享可解商。$p\mid d-1$ 的有限分支分离情形和纯 $p$ 幂的线性化情形分别处理。[基线 160–185 行](https://github.com/Heinz1729/monomial-blocking-curves/blob/75326b5091df2a99b4c9e0354d1e7292ee5d61bb/Manuscript.html#L160-L185) · [固定次数稿 §6.2](Manuscript.html#wild-socle) · [Reid，§2.2 分类表](https://arxiv.org/pdf/2211.06848#page=8)

**§11，常数域与点数。** 对算术群在常数商中的 $q$ 次 Frobenius 陪集，二重传递性保证每个坐标可在同一陪集中调成错排。取对应扭曲的光滑射影模型。设 $D=d!$，单因子几何亏格为 $g_0$。基线估计模型亏格至多 $\ell(g_0+1)D^\ell$。修订稿改为逐根添入有理函数域。设旧域、新域在基底上的次数为 $N,N'=eN$，则 Castelnuovo–Severi 给出 $g'/N'\le g/N+(e-1)/d$。每个平移的第 $j$ 个根满足 $e\le d-j+1$，故 $g_\ell\le\ell(d-1)|H|/2$，其中 $H$ 是几何复合群。这个界消除了 $g_0$，并对所有野特征一致。

位于分支值上方的有理点至多 $(\ell+1)D^\ell$。故 $\ell=\lfloor c\log q\rfloor$、$c<1/(2\log D)$ 时有未分歧有理点，估计对每个平移集一致。审阅时须同时核对所选算术陪集、扭曲的全常数域以及删去分支点后的严格正性。Lean 已检查抽象二重传递陪集中的错排存在性和数值阈值。将该结论应用于实际野覆盖的单群直积、亏格及扭曲由纸面证明给出。[基线 186–202 行](https://github.com/Heinz1729/monomial-blocking-curves/blob/75326b5091df2a99b4c9e0354d1e7292ee5d61bb/Manuscript.html#L186-L202) · [固定次数稿 §6.3](Manuscript.html#wild-twists) · [Kosters，定理 2](https://hrcak.srce.hr/file/274189#page=3) · [Stichtenoth，定理 3.11.3](https://doi.org/10.1007/978-3-540-76878-4) · [Lean 陪集引理](lean/FrobeniusCoset.lean)

## 三次的迹估计

**§§12–14，两个移动点。** 在 $p>3$、$q\equiv2\pmod3$ 下，开集为有序对 $v\ne w,\ v,w\notin-S$。在复数配置空间上，两个半球的弧给出两组子午圈。仅用不同标记的异侧圈可交换。有限标记在对应三次因子上给出两个不同对换。对非平凡无符号张量得到 $b_1\le4\ell+2$。一个符号因子给出 $b_1\le2$。两个符号且其余全平凡时给出 $b_1\le1$，其余含至少两个符号的情形消失。

审阅时须核对生成元包括无穷远标记，及张量商空间允许使用的基。在标准表示中两个对换通常不能同时对角化。Lean 对满足所列关系的子午圈模型计算交叉余循环模余边界。具体覆盖的拓扑模型在手稿中识别。[基线 203–233 行](https://github.com/Heinz1729/monomial-blocking-curves/blob/75326b5091df2a99b4c9e0354d1e7292ee5d61bb/Manuscript.html#L203-L233) · [固定次数稿 §9](Manuscript.html#cubic-cocycles) · [Fadell–Neuwirth 忘点纤维化](https://doi.org/10.7146/math.scand.a-10517) · [余循环](lean/CubicCocycles.lean) · [无符号张量](lean/CubicUnsigned.lean)

**§§15–16，转移到正特征。** 应在同一光滑固有相对模型上核对边界的正规交叉性，包括 $(\infty,\infty)$ 的吹起，并对每个模 $2^j$ 的系数层应用低阶基变换。排序根的挠子在几何一般纤维的连通性经零阶比较传递。一阶比较与对偶识别三阶紧支撑上同调维数。

仿射消没、顶维不变量、驯 Euler 特征和权界共同给出基线式 (12.1)。归一化后的误差为 $O(\ell^2 4^\ell/q+\ell 2^\ell/\sqrt q)$，其常数对 $S$ 一致。代入 $\ell=\lfloor c\log q\rfloor$ 得到 $c<1/\log4$。Lean 中 `SurfaceLaws` 的各字段列出此处需要在具体层上实现的几何等式。其后的秩、维数求和及数值正性已在内核中证明。[基线 234–254 行](https://github.com/Heinz1729/monomial-blocking-curves/blob/75326b5091df2a99b4c9e0354d1e7292ee5d61bb/Manuscript.html#L234-L254) · [固定次数稿 §10](Manuscript.html#cubic-comparison) · [SGA 1，XIII，推论 2.9 与 §2.10](https://arxiv.org/pdf/math/0206203#page=304) · [Deligne，Weil II](https://doi.org/10.1007/BF02684780) · [曲面上的 Lean 输入](lean/CubicSurfaceTrace.lean)

**§18，特征 2 的固定斜率。** 在代数闭包上写 $t=z^3+z^{-3}$，主三次根可取 $x=z+z^{-1}$。在 $z=1$ 取 $w=z-1$，惯性对合 $z\mapsto1/z$ 满足 $\operatorname{ord}_w(\tau(w)-w)=2$。故 $I_0=I_1=C_2,\ I_2=1$。无穷远的惯性为驯的 $C_3$。

平移后的有限分支点互异，在每一有限分支点其余因子几何局部未分歧。几何直积和算术群的嵌入因此可以在不预设常数域的条件下分别验证。对每个秩 $r$ 项，各有限分支的 Swan 至多为 $r$。对所有非平凡张量求和后，总误差不超过 $(2\ell-1)(4^\ell-1)\sqrt q$。这条曲线估计单独给出特征 2 的 $1/\log16$。Lean 已证实际临界值与局部多项式恒等式。`CurveLaws` 中具体覆盖的惯性、导子、迹、对偶和权仍需由几何实现。[基线 288–296 行](https://github.com/Heinz1729/monomial-blocking-curves/blob/75326b5091df2a99b4c9e0354d1e7292ee5d61bb/Manuscript.html#L288-L296) · [固定次数稿 §13](Manuscript.html#cubic-char2) · [局部方程和逐特征标界](lean/CubicCurveTrace.lean)

## 有理点计数与共同补点

`CubicPairCount.lean` 共 71 行。逐行核对的结果如下。其几何起点为原来的齐次射影阻塞条件等价于所有有限斜率的图像命中条件。[基线源文件](https://github.com/Heinz1729/monomial-blocking-curves/blob/75326b5091df2a99b4c9e0354d1e7292ee5d61bb/lean/CubicPairCount.lean) · [射影等价](lean/Projective.lean)

| 行 | 所核对的等式与前提 |
| --- | --- |
| 1–18 | 在实际有限域上定义 $t_\alpha=2(v+w+2\alpha)/(v-w)$。先排除 $v=w$、$v\in-S$ 或 $w\in-S$，再要求对每个 $\alpha$ 三次式均无域内根。`escapeCount` 是有序点对的基数。 |
| 19–38 | 由立方满射解出 $4u^3=v-w$，由 $2\ne0$、$v\ne w$ 得 $4,u\ne0$。应用斜率 $3u^2$ 和截距 $(v+w)/2$ 的阻塞性，所得 $x/u$ 是被排除的根。因此阻塞推出计数为零。只使用这一方向。 |
| 40–48 | `blocking_card_lower_of_trace` 将刚得到的零代入假设 `traceDeviation`。在 $q\ge16$ 时推出含 $\log4$ 的严格数值下界。 |
| 50–54 | `fixedEscapeCount` 数固定斜率 1 的截距，排除 $b=-\alpha$ 并逐参数检测 $x^3-x-b=\alpha$ 无解。$b=-\alpha$ 本来就有根 $x=0$。 |
| 55–71 | 直接对斜率 1 用射影阻塞性，故固定斜率计数也为零。调用 `fixedSlopeDeviation` 后才推出含 $\log16$ 的下界。该蕴含本身无需特征 2，具体的第 18 节输入使用特征 2。 |

基线程序用模三次多项式的 Frobenius 幂和逐线直接试根两种方法交叉复算。例如 $q=47,\ S=\{0,1\}$ 时有 240 个有序三轮换点，对应 $m=3u^2$ 的 **120 条**遗漏线。全斜率下同时遗漏这两个固定参数的线另有 **240 条**。固定两条线时共同遗漏的参数数目又是另一种计数。在 $\mathbb F_5$ 固定斜率 1，截距对 $(0,1)$ 和 $(0,2)$ 分别给出 1 和 0。可在仓库根目录运行 `python checks/cubic_pairs.py` 重现。[复算程序](checks/cubic_pairs.py) · [双线求和与双平移公式](lean/CubicDoubleMiss.lean)

**§17，大域上的共同补点。** 取同一个 Laurent 分支 $E_t$，在其中为每条残余线添入一个满足 $x_i^3-m_i x_i-b_i=\alpha$ 的根。全常数域为 $\mathbb F_q$，相对次数 $[E_t:\mathbb F_q(\alpha)]\le3^t$。Castelnuovo–Severi 给出几何亏格上界，Hasse–Weil 给出光滑射影模型的有理位总数下界，再删去至多 $3^t$ 个参数极点。只有剩余位给出共同命中参数。

独立核对时应在同一选定分支上使用这两个不等式。对应分裂域的次数可大于 $3^t$。Lean 已验证分支、全常数域、零根和单根域的亏格零、有理纤维次数界及专化。$L=\log q\le3^9$ 的次阶上界为无条件 Lean 定理。满足 $q\equiv2\pmod3$ 的全部域阶上，Lean 定理仍要求在多根分支上给出上述亏格不等式和点数定理。[基线 255–286 行](https://github.com/Heinz1729/monomial-blocking-curves/blob/75326b5091df2a99b4c9e0354d1e7292ee5d61bb/Manuscript.html#L255-L286) · [固定次数稿 §12.2](Manuscript.html#cubic-rational-fibres) · [Stichtenoth，定理 3.11.3](https://doi.org/10.1007/978-3-540-76878-4) · [Lean 的射影最小值定理](lean/CubicLogLog.lean)

## 变次数稿的验证范围

范数幂族的精确公式、分圆 Frobenius 族 $m\mid n$ 的两侧界、$m\nmid n$ 的上界及 $m=n=2$ 的精确值均有无条件射影最小值定理。

对 $m\nmid n$ 的下界，手稿按 $n\ge4m$、$2\le n<4m$ 及 $n=1$ 处理。在大扩张次数中，至多一个退化分支的全部 $0$ 或 $s$ 个有理原像必须计入。总候选数仍 $M\le2m\ell$。乘法特征正交展开的系数绝对值之和为 1，所以单个完整和的 Weil 误差不会再乘 $m^M$。Lean 已覆盖逐项完整和估计到正计数的蕴含及对数范围内的一致预算。实际一元 Weil 定理和两种多项式族与该接口的完整衔接仍由手稿给出。[基线 336–389 行](https://github.com/Heinz1729/monomial-blocking-curves/blob/75326b5091df2a99b4c9e0354d1e7292ee5d61bb/Manuscript.html#L336-L389) · [变次数稿 §6](VariableDegree.html#extension-dichotomy) · [Lean 逐项覆盖表](lean/README.md#扩张次数的整除二分律) · [Lidl–Niederreiter，定理 5.41](https://doi.org/10.1017/CBO9780511525926)
