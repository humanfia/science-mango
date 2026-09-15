# M6 第一阶段：固定 supports 的距离稳定律

已得到一个无限参数类上的自然语言证明，并通过 harness 的独立双审阅。

- [完整证明](PROOF.md)
- [整合与范围记录](integration-decision.json)
- [审阅 A](call-011-review.json)、[审阅 B](call-012-review.json)
- [可执行算法与验证](verify_optimizer.py)、[验证结果](verification.json)
- [原始候选](candidate.json)、[依赖哈希](dependency-manifest.json)

令 G=gcd(a,b)，a₀=a/G，b₀=b/G，R=max(deg a,deg b)，
r=max(deg a₀,deg b₀)，D=wt(a₀)+wt(b₀)，K=R(D−1)−r。
固定非平凡完整 signature F。对固定的连通、等权 supports，凡
N>RD 且 gcd(G,xᴺ+1)=F，都有

    d(N) = min_{deg c≤K, F∤c} [wt(a₀c)+wt(b₀c)]。

右侧与 N 无关，可用有限动态规划精确计算，含偶数 N 和重复因子。
例如 A={0,3}、B={0,1} 时，每个 N>12 的距离均为 4。

320 个小规模多项式优化案例与集合运算穷举逐一一致；18 个环码距离
与独立矩阵枚举一致。另含 F=1、重复因子和阈值以下不稳定的检查。
这些有限验证不是无限定理的证明，代码本身不在先前双审阅范围内。

复现：在本目录执行 `python3 verify_optimizer.py`，仅需 Python 标准库。

未完成：随 N 改变 supports 的统一距离分类、全部阈值以下距离、M7；
尚未 Lean 形式化。此结果按明确范围整合，不宣布全部 M6 完成。
