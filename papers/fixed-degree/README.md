# 第一篇 · 固定次数的对数界

设 $`p=\operatorname{char}\mathbb F_q`$，$`L=\log q`$。$`B(q,d)`$ 表示图像族的阻塞数，$`B_{\rm cusp}(q,d)`$ 表示尖点族的阻塞数。两者都取能与所有有理射影直线相交的最少平移数。表中“中文 §”与“英文 §”分别沿用各自手稿的编号。

[中文 PDF](../../Manuscript.pdf) · [中文 HTML](../../Manuscript.html) · [英文 PDF](FixedDegreePencils.pdf) · [英文 LaTeX](FixedDegreePencils.tex) · [英文投稿要点](FixedDegreePencils-highlights.txt) · [全仓成果状态](../../STATUS.md)

## Solved

以下结论在各行列出的适用范围内已有 Lean 证明。

| 结果 | 手稿 | Lean 证明 |
| --- | --- | --- |
| **同域同次数的精确值。** 取 $`d=s`$。在 $`q=s^2`$、$`s\ge2`$ 时，尖点族与图像族的最小值分别为 $`3`$、$`2s-1`$。在 $`q=s^3`$、$`s\ge4`$ 时分别为 $`4`$、$`3s-2`$。两组最小值均可由非平凡阻塞集达到，因而两族阻塞数之比可无界。 | [英文 §5 定理](FixedDegreePencils.tex#L744) · [中文 §15.2](../../Manuscript.html#L261) | [二次扩张](../../lean/CuspidalNormMinimum.lean#L129) · [三次扩张](../../lean/CuspidalNormMinimum.lean#L140) · [尖点族非平凡性](../../lean/CuspidalNontrivial.lean#L51) · [图像族非平凡性](../../lean/NontrivialPencil.lean#L12) |
| **纯 Frobenius 次数的精确值。** 对 $`q=p^h`$、$`d=p^e`$、$`h,e\ge1`$、$`g=\gcd(h,e)`$，有 $`B(q,d)=1+(h/g)(p^g-1)`$。当 $`h\mid e`$，唯一阻塞参数集为全域。当 $`h\nmid e`$，有非平凡的最优解。 | [中文 §1](../../Manuscript.html#L27) | [最小值](../../lean/Paper.lean#L16) · [整除边界](../../lean/NontrivialPencil.lean#L42) · [非平凡最小值](../../lean/NontrivialPencil.lean#L70) |
| **三次置换的上界。** 设 $`q\equiv2\pmod3`$。当 $`q\ge16`$ 时，$`B(q,3)\le 2L/\log3+8`$。在 $`L\le3^9`$ 的整个范围内，Lean 也已证明 $`B(q,3)\le(2L-\log L)/\log3+17`$，包括特征 2。每条非水平线恰好遗漏 $`(q+1)/3`$ 个平移参数。 | [中文 §11 双计数](../../Manuscript.html#L169) · [§12 上界](../../Manuscript.html#L173) | [单线精确计数](../../lean/CubicDoubleMiss.lean#L185) · [一般域阶上界](../../lean/CubicCovering.lean#L148) · [有限范围的次项](../../lean/CubicLogLog.lean#L46) |
| **两族的射影模型与尖点族上界。** 对 $`d\ge2`$，两族的齐次方程几何不可约。尖点族在任意特征满足 $`B_{\rm cusp}(q,d)\le2d\log(2q)+1`$。在 $`p\gt 3`$、$`q\equiv2\pmod3`$ 的三次情形，尖点族的非水平漏线数精确等于两参数有序对计数。 | [英文 §3 尖点族](FixedDegreePencils.tex#L340) · [英文 §4 有序对](FixedDegreePencils.tex#L492) | [图像族不可约性](../../lean/GeometricIrreducibility.lean#L87) · [尖点族不可约性](../../lean/CuspidalGeometry.lean#L51) · [对数上界](../../lean/CuspidalGeneralUpper.lean#L39) · [漏线计数](../../lean/CuspidalTransfer.lean#L118) |
| **尖点族的野惯性与逐根塔。** 对分支值已分开的平移集，零纤维上方的惯性固定其余坐标。在实际复合分裂域内逐根添入，得到覆盖次数至多 $`(d!)^\ell`$，其中 $`\ell`$ 是平移数。 | [中文 §15.1 局部因子](../../Manuscript.html#L249) · [逐层次数](../../Manuscript.html#L254) | [惯性作用](../../lean/CuspidalRootInertia.lean#L183) · [单坐标置换](../../lean/CuspidalSheetAction.lean#L32) · [覆盖次数](../../lean/CuspidalRootDegrees.lean#L172) |
| **尖点族的 Frobenius 扭曲与特化。** 对 $`d\ge3`$ 的非零斜率，实际不动域扩常数后恢复原几何覆盖，覆盖次数和几何亏格均保持。每个好有理位置上的两个根置换在每个坐标的对称群中分别共轭，这足以传递同时错排。 | [中文 §15.1 下降与约化](../../Manuscript.html#L256) | [扩常数同构](../../lean/CuspidalTwistBaseChange.lean#L50) · [次数](../../lean/CuspidalTwistDegree.lean#L57) · [几何亏格](../../lean/CuspidalTwistGenus.lean#L106) · [逐坐标特化](../../lean/CuspidalRationalSpecialization.lean#L107) |

## Conditional

以下定理的 Lean 陈述显式接收几何输入。每项右栏给出条件成立后能推出的结论。

| 定理及所需输入 | 手稿 | Lean 条件与推导 |
| --- | --- | --- |
| **尖点族全特征对数下界。** 对固定 $`d\ge3`$ 和 $`0\lt c\lt 1/(2\log(d!))`$，充分大的 $`q`$ 上有 $`B_{\rm cusp}(q,d)\gt cL`$。域阶阈值对所有平移集一致。输入为实际逐根塔的 Castelnuovo–Severi 不等式和扭曲下降域的 Hasse–Weil 下界。二次尖点族另由已证的射影等价归约到二次图像族。 | [英文 §3 定理](FixedDegreePencils.tex#L330) · [中文 §15.1 一致误差](../../Manuscript.html#L258) | [两个输入](../../lean/CuspidalDescendedLower.lean#L41) · [一致的对数结论](../../lean/CuspidalDescendedLower.lean#L61) · [二次归约](../../lean/CuspidalGeneral.lean#L70) |
| **奇特征三次置换的 $`1/\log4`$ 下界。** 当 $`p\gt 3`$、$`q\equiv2\pmod3`$、$`q\ge16`$，两参数估计给出 $`(L-2\log L)/\log4-5`$ 的严格下界，适用于图像族与尖点族。输入涉及具体单值作用、正特征比较、迹公式和 Frobenius 权界。 | [英文 §4 定理及误差](FixedDegreePencils.tex#L473) · [中文 §11 统一阈值](../../Manuscript.html#L162) | [曲面输入](../../lean/CubicSurfaceTrace.lean#L307) · [图像族下界](../../lean/CubicSurfaceTrace.lean#L395) · [尖点族下界](../../lean/CuspidalTransfer.lean#L147) |
| **特征 2 的 $`1/\log16`$ 下界。** 对 $`q=2^{2h+1}`$、$`q\ge16`$，固定斜率估计给出 $`B(q,3)\gt (L-2\log L)/\log16`$。输入包括局部单值、有限分支的 Swan 导子、迹公式和权一界。 | [中文 §13](../../Manuscript.html#L206) | [曲线输入](../../lean/CubicCurveTrace.lean#L114) · [射影下界](../../lean/CubicCurveTrace.lean#L154) |
| **三次负次项上界的全域版本。** 对所有 $`q\equiv2\pmod3`$ 有 $`B(q,3)\le(2L-\log L)/\log3+17`$。超出上列无条件范围时，用所构造 Laurent 分支上的 Castelnuovo–Severi 与 Hasse–Weil 控制残余漏线的共同补点。 | [中文 §12 上界](../../Manuscript.html#L173) · [§12.2 几何输入](../../Manuscript.html#L196) | [分支上的条件](../../lean/CubicLogLog.lean#L30) · [全域上界](../../lean/CubicLogLog.lean#L75) |
| **一般次数的分斜率上界。** 当 $`p\nmid d(d-1)`$ 且 $`\gcd(d,q-1)=1`$ 时，首项系数可取 $`2/\log(1/\delta_d)`$，其中 $`\delta_d`$ 为错排比例。非置换次数还要计入水平线。有效 Chebotarev 控制驯情形的非水平遗漏率；坏特征碰撞估计使用 Kummer 曲线点数界。对 $`p\nmid d`$，负 $`\log L`$ 次项还使用补点分支上的 Castelnuovo–Severi 与 Hasse–Weil。 | [中文 §14 分斜率估计](../../Manuscript.html#L216) · [§14.1 碰撞与补点](../../Manuscript.html#L221) | [驯情形](../../lean/PencilPaperBounds.lean#L69) · [Kummer 情形](../../lean/PencilPaperBounds.lean#L82) · [共同补点](../../lean/PencilPaperBounds.lean#L48) |

## Open

| 类型 | 问题或形式化缺口 | 手稿 | 已有 Lean 结果或待证接口 |
| --- | --- | --- | --- |
| 数学问题 | 对 $`p\gt 3`$、$`q\equiv2\pmod3`$ 的三次置换图像族，$`B(q,3)/\log q`$ 是否收敛？最优首项常数和真实次项仍未确定。手稿给出的下极限与上极限界分别为 $`1/\log4`$ 和 $`2/\log3`$。 | [中文 §7 定理 3](../../Manuscript.html#L122) · [§11 未决问题](../../Manuscript.html#L167) | [当前条件式下界](../../lean/CubicSurfaceTrace.lean#L395) · [当前无条件上界](../../lean/CubicCovering.lean#L148) |
| 形式化 | **图像族全特征定理。** 手稿证明了每个固定 $`d\ge2`$ 都有 $`B(q,d)=\Theta_d(\log q)`$，下极限系数至少 $`1/(2\log(d!))`$。驯分支的较强常数见中文定理 1。一般次数的复合单值群、亏格估计及扭曲有理点与实际图像族下界之间仍缺完整的 Lean 连接。 | [英文 §2 总定理](FixedDegreePencils.tex#L153) · [中文 §2 驯情形](../../Manuscript.html#L32) · [§6 全特征](../../Manuscript.html#L78) | [三次避碰](../../lean/CubicSlope.lean#L58) · [陪集错排](../../lean/FrobeniusCoset.lean#L33) · [误差窗口](../../lean/FixedDegreeBudget.lean#L12) |
| 形式化 | **尖点扭曲的两个曲线不等式。** 在本库的正则微分与有理位置定义下，逐根塔的 Castelnuovo–Severi 不等式和下降域的 Hasse–Weil 下界尚待形式化。当前下界直接使用扩常数后的几何亏格；另行比较扩常数前后内蕴正则微分的维数还需基变换定理。 | [英文核验范围](FixedDegreePencils.tex#L849) · [中文逐根塔与扭曲](../../Manuscript.html#L255) | [Castelnuovo–Severi 接口](../../lean/CuspidalCompositumGenus.lean#L19) · [Hasse–Weil 接口](../../lean/CuspidalDescendedLower.lean#L18) · [已证几何亏格](../../lean/CuspidalTwistGenus.lean#L106) |

[研究时间线与关键提交](../../TIMELINE.md) · [仓库首页](../../README.md)
