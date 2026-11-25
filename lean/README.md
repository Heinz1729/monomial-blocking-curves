# 有限域上单项式曲线的竖直平移与阻塞数

本工程对应配套中文手稿。主定理以射影直线与齐次曲线的原始方程为起点。最小值使用 Lean 的 `IsLeast`，同时断言存在达到该数的有限参数集，而且任一可行集都至少有这么多元素。

## 复现

需要 Git 和 Lean 版本管理器 elan。进入本文件所在目录后运行以下命令。首次运行时，Lake 会按锁文件获取 mathlib 及其依赖。

```sh
lake exe cache get
lake build
lake env lean BlockingCurves.lean
```

项目选择 Lean 4.8.0。mathlib 锁定为版本 v4.8.0，提交 `b5eba595428809e96f3ed113bc7ba776c5f801ac`。最后一条命令列出各项结果依赖的公理。构建已允许使用官方 mathlib 二进制缓存。全部交付的定理均从本包中的 Lean 源文件编译；八元域和四十一元域的有限计算证书使用内核归约。验证记录见 `verification.txt`。

## 读代码

| 手稿中的结果 | 代码入口 |
| --- | --- |
| 次数为 p 的幂时，完整射影问题的精确最小值 | `Paper.lean`，`BlockingCurves.projective_prime_power_minimum` |
| 原始齐次曲线与逐线仿射判据等价，涵盖无穷远线 | `Projective.lean`，`projectiveBlocks_iff_graphHits` |
| 任意有限域扩张上的迭代 Frobenius 及不动域次数 | `Frobenius.lean`，`iterated_frobenius_minimum` |
| scattered 映射的充要刻画及其精确阻塞数 | `GeneralGeometry.lean`，`scattered_iff_forall_graphHits_iff`；`MainResult.lean`，`exact_scattered_minimum` |
| 仿射超平面阻塞的经典上、下界 | `UpperBound.lean`，显式坐标轴构造；`LowerBound.lean`，有限域多项式求和 |
| 四十一元域上的三次曲线族全局最小值 5 | `CubicGlobal.lean`，`BlockingCurves.Cubic41.projective_cubic_minimum` |
| 所有五元素最优集、仿射轨道以及精确数量 328 | `CubicOrbit.lean`，`projective_cubic_orbit`、`orbit_card` |
| 四十七元域三次曲线的最小值 5 | `Cubic47Global.lean`，`BlockingCurves.Cubic47.projective_cubic_minimum` |
| 四十七元域最优集的单轨道分类、平凡稳定子和精确数量 2,162 | `Cubic47Orbit.lean`，`projective_cubic_orbit`、`stabilizer_exact`、`orbit_card` |
| 固定含 0、1 后穷举四十七元域的 990 个四元集和 14,190 个五元集 | `Cubic47.lean`、`Cubic47Semantics.lean`、`Cubic47Symmetry.lean` |
| 规范化、枚举的模型及其与模 41 方程的桥接 | `CubicSymmetry.lean`、`Cubic41.lean`、`Cubic41Semantics.lean`、`CubicGlobal.lean` |
| 八元域的独立小例子，256 个参数集、56 个最优集 | `F8Example.lean`，只需 Lean 4.8.0 核心库 |

## 来源与研究范围

期刊版问题 5.4 问一般的有限域与次数。本文给出 Frobenius 次数子族和两个非 Frobenius 三次例子的精确答案。已有的仿射阻塞数定理归于 Jamison、Brouwer 和 Schrijver。首版检索日期为 2026 年 11 月 25 日，文献检索与优先权边界详见手稿。四十七元域的代表元与计算分类由 Dot 提出。[原问题](https://doi.org/10.1007/s10623-026-01958-z) · [经典阻塞数定理](https://ir.cwi.nl/pub/9858/9858D.pdf)
