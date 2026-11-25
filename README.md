# 有限域上单项式曲线的竖直平移与阻塞数

研究手稿与 Lean 形式化署名 **GPT-Astra**（AI）。[阅读中文手稿（PDF，6 页）](Manuscript.pdf) · [HTML 源文件](Manuscript.html)

在有限域上，把曲线 $y=x^d$ 上下平移，最少需要多少个平移参数，才能使每条有理射影直线都与其中一条曲线相交？本稿研究 Asgarli、Ghioca 和 Yip 提出的问题 5.4 的两个特例。[原论文](https://doi.org/10.1007/s10623-026-01958-z)

* 当 $q=p^h$、$d=p^e$ 且 $g=\gcd(h,e)$ 时，最少需要 $1+(h/g)(p^g-1)$ 条曲线。证明把问题化为不动域上的仿射超平面阻塞问题。取一组基，所有坐标轴的并集就给出最优参数集。
* 当 $q=41$、$d=3$ 时，最少需要 5 条曲线。令 $H=\{1,10,16,18,37\}$，所有最优参数集恰为 $uH+v$（$u\ne 0$），共 328 个。

## 复核证明

在 [lean/](lean/) 目录运行下面的命令。工程使用 Lean 4.8.0，mathlib 版本由锁文件固定。

```sh
cd lean
lake exe cache get
lake build
lake env lean BlockingCurves.lean
```

[代码索引](lean/README.md)列出各项定理的入口。[原始验证记录](lean/verification.txt)包含构建结果、公理依赖和源文件哈希。研究手稿与形式陈述的对应关系仍待独立审阅。

## 彩蛋

[RMM 2026 六题中文答卷（PDF）](bonus/RMM-2026-中文答卷.pdf) · [HTML 源文件](bonus/RMM-2026-中文答卷.html)。答卷附有组委会两天的原题链接，供逐题对照。
