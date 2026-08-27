# Li--Wang--Zhang (2026)：divergence-gradient 随机 Jacobi grounding

审计日期：2026-08-25。

## 来源与模型

L. Li, W. Wang, S. Zhang,
[*Upper and Lower Bounds for The Quantum Dynamics of One-Dimensional
Divergence-Type Random Jacobi Operators*](https://arxiv.org/abs/2601.08796v2),
arXiv:2601.08796v2 (2026-01-20)，研究

```text
(H_a u)_n = -a_{n+1}u_{n+1} + (a_{n+1}+a_n)u_n - a_nu_{n-1}
```

且假设 `a_n` iid、严格正并有统一上下界。

## 与冻结随机质量算子的精确映射

对冻结质量令 `a_n=m_n^{-1}`。有限周期中，本地已经通过 Gram/AB--BA 桥证明
`M^{-1/2} D^T D M^{-1/2}` 的非零谱与 `D M^{-1} D^T` 相同。因此论文的
divergence-gradient 谱模型与目标随机质量谐波谱有精确的非零谱对应，而不是只靠物理类比。

## 可借用的定理

论文 Theorem 2.1 给声学端 IDS 渐近

```text
N(E) = sqrt(E) / (pi * sqrt(kappa)) + O(E),
kappa = (E[a_0^{-1}])^{-1}.
```

冻结分布下 `a_0^{-1}=m_0` 且 `E[m_0]=1`，所以形式常数化为
`N(E)=sqrt(E)/pi+O(E)`。这与本地 clean-cycle 谱夹逼所得的定性
`sqrt(E)` 声学计数尺度一致。

论文还给正能量 Lyapunov 指数的低能渐近，并指出 localization length 在
`E -> 0+` 时按 `E^{-1}` 发散；用频率 `omega=sqrt(E)` 表示即为
`omega^{-2}`。

## faithful borrowing 边界

可借路线是 Gram 谱桥、Pruefer phase/oscillation counting、声学 IDS 双边界和低能
transfer-matrix large-deviation 的组织方式。

不可借入的是有限周期 eigenprojector marks、三腿 overlap 联合经验极限、共振面密度、
非线性 kinetic-time remainder 或完整热化律。论文结论不作为 Lean 公理；若使用其
`sqrt(E)` 精确常数，仍须在本地从相位迭代逐步重证。
