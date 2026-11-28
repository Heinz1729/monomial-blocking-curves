# 成果与核验状态

本页按论文定位定理，再单列两篇共用的有限证书。状态以 [768cfbb 的证明与公理记录](https://github.com/Heinz1729/monomial-blocking-curves/blob/768cfbb8db344f3e7749e5061370a7493321cca6/lean/verification.txt) 为准。

| 状态 | 第一篇 · 固定次数与尖点族 | 第二篇 · 变次数与系数周期 |
| --- | --- | --- |
| **Solved** · Lean 已证 | [同域精确值、三次上界、尖点扭曲与特化](papers/fixed-degree/README.md#solved) | [Frobenius 幂、水平覆盖、范数幂与整除侧](papers/variable-degree/README.md#solved) |
| **Conditional** · 含明示的数学输入 | [三次迹估计、尖点下界与全域补点上界](papers/fixed-degree/README.md#conditional) | [水平覆盖的渐近推论、非整除侧字符和下界](papers/variable-degree/README.md#conditional) |
| **Open** · 数学问题或形式化缺口 | [三次最优常数、图像族全特征证明及两条曲线不等式](papers/fixed-degree/README.md#open) | [置换单项式的平方根上界、Weil 界与实例的形式化](papers/variable-degree/README.md#open) |

每份定理表都给出陈述适用的域与次数、手稿的具体位置，以及 Lean 声明。Open 项的 Lean 链接标出已证的界、可用的引理或所需输入。[完整研究时间线及提交证据](TIMELINE.md)

## 有限域证书

### Solved

| 域与次数 | 已核验的结论 | 手稿 | Lean 证明 |
| --- | --- | --- | --- |
| $`q=8,\ d=2`$ | 最少 4 条，恰有 56 个最优参数集。 | [计算附录](FiniteCertificates.html#L24) | [四元见证](lean/F8Example.lean#L39) · [最小值下界](lean/F8Example.lean#L42) · [射影语义](lean/F8Semantics.lean#L98) · [56 个解](lean/F8Semantics.lean#L106) |
| $`q=32,\ d=6`$ | 最少 7 条。 | [计算附录](FiniteCertificates.html#L55) | [射影最小值](lean/Sextic32Global.lean#L120) |
| $`q=41,\ d=3`$ | 最少 5 条，328 个最优集构成一个仿射轨道。 | [计算附录](FiniteCertificates.html#L39) | [最小值](lean/PrimeFieldInstances.lean#L8) · [轨道分类](lean/CubicOrbit.lean#L97) · [基数](lean/CubicOrbit.lean#L195) |
| $`q=47,\ d=3`$ | 最少 5 条，2,162 个最优集构成一个仿射轨道。 | [计算附录](FiniteCertificates.html#L50) | [最小值](lean/PrimeFieldInstances.lean#L14) · [轨道分类](lean/Cubic47Orbit.lean#L56) · [基数](lean/Cubic47Orbit.lean#L82) |

### Open · 形式化

| 结论与核验边界 | 手稿 | 当前证明与复算 |
| --- | --- | --- |
| 32 元域中 10,912 个最优集分成 11 个仿射轨道。两种归一化穷举给出相同结果。Lean 已证最小值；完整轨道分类仍待形式化。 | [轨道与双计数](FiniteCertificates.html#L61) | [已证的最小值](lean/Sextic32Global.lean#L120) · [独立枚举与轨道检查](checks/sextic32.py#L119) |

[首页](README.md) · [计算附录 PDF](FiniteCertificates.pdf) · [独立射影陈述](lean/ProblemStatement.lean) · [审阅记录](REVIEW.md)
