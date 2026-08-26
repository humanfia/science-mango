# Frozen v0.3 随机质量 FPUT：一手文献 grounding 审计

**审计日期：2026-08-24。** 这是独立文献账本；不改变 campaign DAG、节点状态或
release certificate。

## 0. 审计对象、证据等级与裁决口径

冻结目标是：一维周期链，`m_j` iid `Uniform[4/5,6/5]`，

```text
U_g(r) = r²/2 + (κg/3) r³ + (βg²/4) r⁴,   β > 2κ²/9,
```

只删平移零模、保留其余 `N-1` 个模；初态是指定的 random-phase 非平衡能谱；
observable 是 late-window 归一化模态能量相对均匀分布的全模 `l1` 距离。第一目标为
`T_eq = Theta_P(g^-2)`，增强目标为 `g² T_eq -> tau_* > 0`（依概率）。

四个待解除节点简称：

- **B1** `transfer.exact_kernel_identification`；
- **B2** `transfer.exact_infrared_and_nondegeneracy`；
- **B3** `transfer.exact_kinetic_relaxation`；
- **B4** `transfer.micro_observable_limit`。

本文采用以下证据等级：

- **R**：论文对其实际模型给出严格数学定理；
- **K**：严格分析的是已经写下的 kinetic equation，而不是微观 Hamilton 流；
- **F**：形式 wave-turbulence / closure 推导；
- **N**：数值实验或物理 scaling 证据。

“直接解除 blocker”要求 source theorem 的模型、随机性、尺度、observable 和量词与
冻结目标一致，或已有一条完全证明的模型等价桥。只提供相似公式、证明技术或数值
scaling 一律记为“不解除”。

## 1. 总裁决

在本次检索覆盖的一手论文中，**没有一篇直接解除 B1--B4 中任何一个**，也没有一篇
证明 frozen v0.3 的 `Theta_P(g^-2)` 或确定性 `tau_*` 极限。

| Blocker | 最强相关结果 | 能借什么 | 尚缺什么 | 直接解除 |
|---|---|---|---|---|
| B1 | Wang 等的有限体积三次顶点与形式三波方程；Bernardin--Huveneers--Olla、Ajanki--Huveneers 的随机谐波谱/transfer-matrix 控制 | 正确的有限 `N` 顶点代数、声学/局域化分层、transfer-matrix 方法 | 带频率、bond leg、局域中心、三模 overlap 和 broadened mismatch 的**联合 marked empirical limit** | 否 |
| B2 | 随机谐波链高频 eigenfunction-correlator；同质量 FPU-beta kinetic 方程的退化碰撞频率与 weighted decay | soft/bulk 分割、退化权重、碰撞不变量分析 | 目标 random three-wave kernel 的红外双边界、resonance-density 补偿、连通性和不变量分类 | 否 |
| B3 | Bricmont--Kupiainen 的 pinned `d>=2` four-wave 近平衡扩散；Germain--La--Menegaki 的 1D homogeneous beta-FPUT 近平衡 weighted relaxation | H-theorem、slow/fast 分解、无谱隙 polynomial bootstrap | 精确 random three-wave kernel、冻结初态 basin 的全局解和定量首达 margin | 否 |
| B4 | Deng--Hani 的 `d>=3` NLS full kinetic-time；Staffilani--Tran 的带噪 `d>=2` lattice ZK three-wave；1D 结果只到 subkinetic time | diagram/cutting/cancellation、resonance broadening、remainder 组织 | 1D、`O(1)` frozen disorder、随机本征基、确定性流、完整 `g^-2` 时间、全模 late-window `l1` 一致概率误差 | 否 |

一个重要的逻辑分界是：

```text
stationary state classification != convergence to that state
kinetic relaxation             != microscopic-to-kinetic limit
T_eq proportional-to g^-2 fit  != tightness or g² T_eq -> tau_*
```

## 2. 与随机质量 / disordered FPUT 最接近的来源

### 2.1 Wang--Fu--Zhang--Zhao (2020) — 最贴近物理模型，但不是严格定理

**来源与版本。** Z. Wang, W. Fu, Y. Zhang, H. Zhao,
[arXiv:1903.09502v2](https://arxiv.org/abs/1903.09502v2), 2019-07-24；
[Phys. Rev. Lett. 124, 186401](https://doi.org/10.1103/PhysRevLett.124.186401)
(2020)。证据等级 **F+N**。

**精确设定。** 一维周期随机质量链，

```text
H = sum_i [p_i²/(2m_i) + (q_{i+1}-q_i)²/2
           + (lambda/n)(q_{i+1}-q_i)^n].
```

质量意图为 iid `Uniform[1-delta_m,1+delta_m]`；arXiv TeX 的一个端点有明显排字不一致，
数值使用 `delta_m=0.2`。在谐波本征基中，论文给出有限 `N` 的 `n` 模 bond-overlap
tensor；complex-amplitude 归一化还带 `product_s (2 omega_{k_s})^(-1/2)`。论文随后**形式上**
写出 `n`-wave kinetic equation，并在碰撞积分非零时读出 `T_eq proportional-to lambda^-2`。

数值固定 `lambda=1`、改变能量密度，使用 `N=511,1023,2047`，每个 disorder
realization 平均 120 组随机相位；初始能量主要放在低 10% 模；late-window 参数
`mu=2/3`。其 spectral-entropy 指标只对上半谱归一化，并以 `xi(T_eq)=1/2` 定义时间。

**实际结论。** 对 homogeneous cubic 链，动量与频率约束禁止三波共振；随机质量破坏
波数 selection rule，有限 `N` tensor 的大量条目数值非零，模拟支持 cubic case 的
`T_eq proportional-to lambda^-2`。论文没有给 Duhamel remainder、经验碰撞测度收敛、
概率误差或 hitting-time 定理。

**对 blocker。** 可作为 B1 的有限体积顶点公式和 collision-data 设计来源；不能直接
解除 B1、B2、B3 或 B4。

**不匹配。** 纯 cubic 势向一侧无界，而冻结势有 `O(g²)` quartic stabilizer；论文
observable 不是全 `N-1` 模 late-window `l1`；没有 `N_min(g)` 联合极限、tightness 或
确定性 `tau_*`。因此这里的 `g^-2` 是物理/数值证据，不能作为无条件 Lean theorem。

### 2.2 Pezzi--Deng--Lvov--Lorenzo--Onorato (2021) — 三波共振几何的干净示例

**来源与版本。** A. Pezzi et al.,
[arXiv:2103.08336v1](https://arxiv.org/abs/2103.08336v1), 2021-03-12。
证据等级 **F+N**。

**精确设定与结论。** 一维**周期二原子**链，质量按轻/重交替而非 iid；相互作用势以
cubic anharmonicity 为主。谐波谱分成 acoustic 和 optical 两支。作者形式推导两条
耦合三波 kinetic equations，证明该形式方程的 H-theorem，并得到新 canonical 变量中的
能量均分平衡。允许的主共振是“两 acoustic + 一 optical”，且只在重/轻质量比小于 3
时存在；确定性数值支持该图景。

**对 blocker。** 可借 resonance-manifold 代数、branch bookkeeping 和 H-theorem
证明形状；不解除任何 blocker。

**不匹配。** 二周期质量不是 frozen iid disorder；动量仍守恒；无 rigorous
micro-to-kinetic limit；纯 cubic 稳定性、时间量词和 observable 均不匹配。

### 2.3 Dhar--Saito (2008) — 只是一类 boundary-driven 数值证据

**来源与版本。** A. Dhar, K. Saito,
[arXiv:0806.4067v1](https://arxiv.org/abs/0806.4067v1), 2008-06-25；
[Phys. Rev. E 78, 061136](https://doi.org/10.1103/PhysRevE.78.061136)。证据等级 **N**。

**设定与结论。** 无序 FPU 链接热浴，研究非平衡稳态热流；低温下，小系统受无序
主导，但作者的数值拟合在大 `N` 回到 `J proportional-to N^(-2/3)`，未发现此前声称的
有限温度 conductivity transition。

**裁决。** 这是开放边界稳态热流，不是孤立链模态均分或 `T_eq`；不能解除 blocker，
也不能拿 conductivity exponent 代替 thermalization-time theorem。

### 2.4 McGinnis--Wright (2024) — 严格 random FPUT，但在 coherent KdV regime

**来源与版本。** J. A. McGinnis, J. D. Wright,
[arXiv:2308.06115v1](https://arxiv.org/abs/2308.06115v1), 2023-08-11；
[Physica D 463, 134154](https://doi.org/10.1016/j.physd.2024.134154) (2024)。
证据等级 **R**。

**精确设定与结论。** 论文的主定理针对满足 Hypothesis 1.1 的“transparent”随机质量：
质量扰动是 iid 随机序列的离散二阶差分，因而是相关的，不是普通 iid 质量。对幅度
`epsilon²`、波长 `epsilon^-1` 的平滑 long-wave 初态，在
`|t| <= T0 epsilon^-3` 上，以概率一由左右行 KdV 解近似；绝对 `l2` 误差为
`O(epsilon² sqrt(|log epsilon|))`。

**对 blocker。** 可借 pathwise energy estimate、随机 homogenization 和 residual
控制写法；不解除 B1--B4。

**不匹配。** coherent long-wave/KdV 极限不是 random-eigenmode kinetic 极限；质量法则
不是 frozen iid uniform；结论不涉及 equipartition、`g^-2` 或 late-window `l1`。论文也
说明普通 iid 质量会产生其透明构造避开的 random-walk obstruction。

## 3. 随机谐波谱、局域化与输运：可严格借用的部分

### 3.1 Bernardin--Huveneers--Olla (2019)

**来源与版本。** C. Bernardin, F. Huveneers, S. Olla,
[arXiv:1710.08848v2](https://arxiv.org/abs/1710.08848v2), 2019-01-07；
[Commun. Math. Phys. 365](https://doi.org/10.1007/s00220-018-3251-4) (2019)。
证据等级 **R**。

**精确假设。** 一维 unpinned **harmonic** chain，正文用有限自由边界；`m_x` iid，法则
有支撑在 `[m_-,m_+]`、`m_->0` 的 smooth compactly-supported density。初态是 local
Gibbs state：`beta in C^0([0,1])` 且严格正，stretch profile `r in C^1` 并在两端为零，
momentum profile `p in C^1`。

**严格结论。** Theorem 1：对任意连续测试函数及固定宏观时间，时间取 `Nt`，stretch、
momentum、energy 的经验场在质量上几乎必然、在 local-Gibbs 初态上取平均后，收敛到

```text
partial_t r = (1/E[m]) partial_y p,
partial_t p = partial_y r,
partial_t e = (1/E[m]) partial_y(r p).
```

温度分量在任意 space-time scale 上冻结。论文使用的高模 EFC 估计是：对
`0<alpha<1/2` 和 `I(alpha)={k>N^(1-alpha)}`，

```text
E[sum_{k in I(alpha)} |psi_k(x) psi_k(y)|]
  <= C exp(-c |x-y| / N^(2 alpha)).
```

由此 Lemma 3 得：若 `2 alpha < gamma < 1`，则几乎必然最终每个这些高模都集中在长度
不超过 `2N^gamma` 的区间外只剩 `N^(-1/gamma)` 级尾部。低频 localization length
按 `omega^-2` 发散，约 `k <= sqrt(N)` 的 acoustic modes 不能用同一局域化估计处理。

**对 blocker。** 这是 B2 最直接的严格可借部件之一，并可为 B1 的 marked mode 空间
提供 soft/bulk split；但不直接解除 B1 或 B2。

**不匹配。** harmonic integrable 流不会 thermalize；observable 是 site-space
hydrodynamic field；初态不是 frozen Haar-phase two-band profile；边界不同。目标 uniform
密度是否逐字满足论文所用 smooth-density 版本应单独检查或通过近似/稳定性证明，不能
默认为自动实例。

### 3.2 Ajanki--Huveneers (2011)

**来源与版本。** O. Ajanki, F. Huveneers,
[arXiv:1003.1076v1](https://arxiv.org/abs/1003.1076v1), 2010-03-04；
[Commun. Math. Phys. 301](https://doi.org/10.1007/s00220-010-1161-1) (2011)。
证据等级 **R**。

**精确假设。** 一维固定边界 harmonic chain，最近邻相同 springs；`n` 个 iid 正质量；
两端接 Casher--Lebowitz Langevin baths，温度 `T_1>=T_n>0`。质量密度 compactly supported
于 `(0,infinity)`，在其支撑内部 `C^1`，导数一致有界。冻结 uniform 法则与该定理陈述的
内部正则性看起来兼容，但实例化仍应在形式化时逐项证明。

**严格结论。** Theorem 1.1 给常数 `K,K'>0`：

```text
K (T_1-T_n) n^(-3/2)
 <= E[J_n^CL]
 <= K' (T_1-T_n) n^(-3/2).
```

证明给低频 `omega <= n^(-1/2+epsilon)` transfer-matrix product 的定量控制；高频贡献
指数小。关键 acoustic 事实是 Lyapunov exponent `gamma(omega)` 在零点按 `omega²`
缩放，因此长度 `n` 的传输由 `omega² n = O(1)` 的层主导。

**对 blocker。** transfer-matrix、低频 cutoff 和小分母概率估计可用于 B2；不解除任何
blocker。

**不匹配。** boundary-driven harmonic steady current 不是孤立非线性链的模态能量松弛；
`n^-3/2` 是热流的 system-size law，不是 `g^-2` equilibration law。

### 3.3 Bernard--Texier (2026) — 只作为低频公式路线，不作 exact kernel 证据

**来源与版本。** M. Bernard, C. Texier,
[arXiv:2506.18693v2](https://arxiv.org/abs/2506.18693v2), 2026-02-04；
[Phys. Rev. E 113, 014143](https://doi.org/10.1103/bc9p-fhyz) (2026)。证据等级 **F/R-mixed**。

**设定与结论。** iid random springs 与 iid random masses 的 harmonic chain。论文用
combinatorial method 给 complex Lyapunov exponent 的 compact **approximate** expression，
并分析 DOS 和 localization 的低/高频 asymptotics。有限 `E[m]`、`E[K^-1]` 时恢复
clean-chain DOS exponent；有限更高矩时 inverse localization length 的低频指数回到
`omega²`。

**裁决。** 可用来选择需要严格证明的 low-frequency formula，但作者明确称核心 compact
expression 为 approximate；不能将其作为 B1/B2 的 exact theorem。它也不含 eigenvector
marks、三次 overlap 或非线性动力学。

## 4. 弱非谐 + disorder 的严格负面约束

### 4.1 Huveneers (2013/2014)

**来源与版本。** F. Huveneers,
[arXiv:1203.3587v5](https://arxiv.org/abs/1203.3587v5), 2014-04-16；
[Nonlinearity 26, 837](https://doi.org/10.1088/0951-7715/26/3/837) (2013)。
证据等级 **R**。

**精确模型。** 任意 `d>=1` 的周期 lattice，每点是**互不耦合且 pinned** 的 harmonic
oscillator；频率 `omega_x` iid，法则有 bounded density，且
`0<omega_-<=omega_x<=omega_+`。弱参数 `epsilon` 同时控制 onsite `U(q_x)` 和邻点偶势
`V(q_x-q_y)`；势光滑、polynomial growth，并满足 pinning domination。可选 velocity-flip
noise 的强度为 `epsilon'`，它保持每个 oscillator 的能量。

**严格结论。** Theorem 1（无噪声）对任意固定整数 `n>=1`、`1<=m<=n`，几乎每个频率
样本有

```text
lim_{t->infinity} limsup_{epsilon->0} limsup_{N->infinity}
epsilon^(-m) <(epsilon/sqrt(epsilon^(-n)t)
  integral_0^(epsilon^(-n)t) J_N ds)^2>_beta = 0.
```

Theorem 2 在 `epsilon'=epsilon^n` 时给相应 Green--Kubo variance 上界
`C(n) epsilon^(n+2)`。证明建立有限邻域 Diophantine nonresonance，并逐阶解局部
homological equation `-A_har u=f`。

**对 frozen v0.3 的含义。** 这不是目标链的反例，但严格说明“disorder + arbitrarily
weak anharmonicity”本身不推出普适 `epsilon^-2` 松弛；必须证明目标的 resonance density
和 network connectivity。可借 local normal form / nonresonance 排除作为 admissible-joint-
limit 的防护条件，不解除 blocker。

**不匹配。** 随机 onsite frequency、pinned 且零阶 oscillators 已解耦；observable 是
equilibrium current；极限顺序先 `epsilon->0` 后长时；不是 random masses、acoustic FPUT
或 isolated full-mode equipartition。

### 4.2 Huveneers--Lukkarinen (2020)

**来源与版本。** F. Huveneers, J. Lukkarinen,
[arXiv:2002.10868v1](https://arxiv.org/abs/2002.10868v1), 2020-02-25；
[Phys. Rev. Research 2, 022034](https://doi.org/10.1103/PhysRevResearch.2.022034)。
证据等级 **R+F+N**，三部分必须分开。

**精确模型。** 一维 translation-invariant pinned chain，

```text
H = sum_x [p_x²/2 + omega_0² q_x²/2
           - omega_0² delta (q_{x-1}q_x+q_xq_{x+1})/2
           + lambda q_x^r/r],
```

`r>2` 偶数，`0<delta<1/2`，dispersion
`omega(k)=omega_0 sqrt(1-2 delta cos(2 pi k))`。窄 phonon band 可能在低阶过程中近似
守恒总 phonon number `N_0`。

**严格结论。** Claim 1：有限周期 `L` 下，若最早能改变 phonon number 的 resonant
过程阶数为 `p`，存在有限阶 canonical transform，使 transformed Hamiltonian 与 `N_0`
的 Poisson bracket 是 `O(lambda^p)`。Claim 2：无限链上存在 quasi-local dressed number

```text
N = N_0 + lambda N_1 + ... + lambda^(p-1) N_(p-1)
```

且 `{H,N}=lambda^p {V,N_(p-1)}`。论文在此之后明确说，为计算实际 decay rate 将加入
额外假设并离开严格论证；`lambda^(-2p)` 的 rate prediction 和 MD 比较不属于 Claim 1/2。

**裁决。** 可为 B4 增加一项必须排除的 prethermal normal-form regime；不解除 blocker。
它警告：即使 kinetic time 是 `lambda^-2`，某些非守恒量也可能在窄带中只在更长时标
松弛。

**不匹配。** 无 disorder、onsite even anharmonicity、pinned 窄带；不是 cubic random-mass
FPUT，也不研究 frozen observable。

## 5. phonon Boltzmann / kinetic relaxation

### 5.1 Spohn (2005) — 三声子平衡态分类是条件性 kinetic 结论

**来源与版本。** H. Spohn,
[arXiv:math-ph/0505025v2](https://arxiv.org/abs/math-ph/0505025v2), 2005-09-01；
[J. Stat. Phys. 124](https://doi.org/10.1007/s10955-005-8088-5)。证据等级 **F+K**。

**精确范围。** 工作模型是三维 harmonic lattice 加弱非二次 onsite potential；Wigner
function 和三声子 phonon Boltzmann equation 由 Gaussian decoupling / Feynman diagrams
**形式推导**。微观 kinetic limit 没有被证明。

对 classical spatially homogeneous three-phonon equation，论文证明能量守恒和 H-theorem。
其 Ergodicity Condition (E) 要求任意两个非零 wave numbers 可由有限碰撞链连接；另需
适当的 dispersion regularity。若 (E) 成立，零 entropy production 的解只有
`W_beta(k)=1/(beta omega(k))`，即能量是唯一 collision invariant。量子版本的
Proposition 12.1 还显式假设 `psi in C^2(T^3)`，且 `det Hess(omega)` 的零集至多余维 1，
据此分类 additive collision invariants。

**对 blocker。** 这是 B2 的“connectivity + invariant classification”以及 B3 的
“unique kinetic equilibrium”接口来源；不解除 B2/B3。唯一 stationary state 加 H-theorem
本身不证明所有解收敛，更不证明微观链收敛到该 kinetic equation。

**不匹配。** `d=3`、translation invariant、momentum delta；目标是 1D frozen random
eigenbasis，无 deterministic wave number。observable 和 hitting law 也不同。

### 5.2 Bricmont--Kupiainen (2007/2008)

**来源与版本。** J. Bricmont, A. Kupiainen,
[arXiv:math-ph/0703014v1](https://arxiv.org/abs/math-ph/0703014v1), 2007-03-02；
[Commun. Math. Phys.](https://doi.org/10.1007/s00220-008-0480-y)。证据等级 **K**。

**精确假设。** 研究的是已给定的 spatially inhomogeneous **four-phonon** Boltzmann
equation。取 `d>=2`、pinning `r>0`，为技术方便使用
`omega(k)=omega_0(k)^2`，其中
`omega_0(k)^2=2 sum_j(1-cos k_j)+r`。初值是平衡 `omega^-1` 的小扰动，且空间上消失；
Banach norm 同时控制 Fourier-space decay 和 mode sup norm。线性化 collision operator
除由两个守恒量产生的零模外有正 spectral gap。

**严格结论。** Theorem 1：充分小初扰动有唯一全局解；slow conserved component 与
显式 heat kernel 的差为 `O(C(t)t^-1/2)`，fast component 与 Fourier-law slaved term 的
差为 `O(C(t)t^-1)`，其中 `C(t)=C log(1+t)` for `d=2`，`d>2` 时有界。Theorem 2 给
diffusive scaling limit 到 nonlinear heat equation。

**对 blocker。** slow/fast decomposition、spectral projection 和 nonlinear bootstrap
可作 B3 模板；不直接解除。

**不匹配。** pinned、`d>=2`、four-wave、近平衡、空间扩散；论文明确指出 unpinned
acoustic 情形无 gap 且不由其分析覆盖。它也不做 microscopic derivation。

### 5.3 Germain--La--Menegaki (2024/2026)

**来源与版本。** P. Germain, J. La, A. Menegaki,
[arXiv:2409.01507v1](https://arxiv.org/abs/2409.01507v1), 2024-09-03；
正式发表版本 [Arch. Ration. Mech. Anal.](https://doi.org/10.1007/s00205-026-02223-2)
(2026)。证据等级 **K**。

**精确假设。** 一维 homogeneous equal-mass beta-FPUT 的 **four-wave kinetic equation**，
`omega(p)=|sin(p/2)|`，带 momentum 和 frequency delta。作者使用非平凡 resonant
manifold 的显式参数化，并说明 microscopic derivation 与 trivial singular resonance
的严格消除仍是 outstanding problem。分析 nonsingular Rayleigh--Jeans equilibrium
`f_(beta,gamma)=1/(beta omega+gamma)`，`beta,gamma>0`。

**严格结论。** collision frequency 满足 `a(p) comparable-to |sin(p/2)|^(5/3)`，所以
无正 uniform gap。Theorem 3：若 `g_0` 与 `Ker L` 正交，则对
`mu,nu in (1/6,1/2)`、任意小 `delta>0`，

```text
||omega^mu exp(tL) g_0||_infinity
 <= C_delta <t>^[-3(mu+nu)/5 + delta]
    ||omega^(-nu) g_0||_infinity.
```

Theorem 4：若 mass/energy perturbations 均为零，且
`||omega^(-1/2)g_0||_infinity=epsilon<epsilon_0`，存在全局解并有

```text
||omega^(1/2)g(t)||_infinity
 <= C epsilon <t>^(-3/5+1/1000).
```

**对 blocker。** 这是 B3 最有价值的 weighted-degenerate relaxation 模板；它也说明
B2 不应要求无权 uniform gap。仍不直接解除 B2/B3。

**不匹配。** equal masses、quartic four-wave、近平衡 nonsingular RJ；目标是 random
three-wave、冻结远离平衡 profile 和 full-mode late-window `l1`。其 `5/3` 红外指数不能
移植到目标 kernel。

## 6. microscopic-to-kinetic limit：可借架构与明确缺口

### 6.1 Lukkarinen--Spohn (2005/2007) — frozen randomness，但只有 weak-disorder linear scattering

**来源与版本。** J. Lukkarinen, H. Spohn,
[arXiv:math-ph/0505075v1](https://arxiv.org/abs/math-ph/0505075v1), 2005-05-27；
[Arch. Ration. Mech. Anal. 181](https://doi.org/10.1007/s00205-006-0005-9) (2007)。
证据等级 **R**。

**精确假设。** 三维 harmonic crystal，
`m_y=(1+sqrt(epsilon) xi_y)^(-2)`；`xi_y` iid、有界、均值零。elastic coupling 指数衰减；
dispersion smooth/even、Morse、满足 dispersive `t^-3/2` 和 crossed-recollision suppression；
并要求 `omega_min>0`，即 pinned/gapped。确定性初始 wave states 独立于 disorder，有统一
能量/tightness，初始 Wigner distributions 收敛。

**严格结论。** Theorem 2.3：在 time/space `O(epsilon^-1)` 上，disorder-averaged Wigner
function 对 Schwartz tests 收敛到 linear Boltzmann Markov jump process；off-diagonal
component 只在时间平均后消失。

**对 blocker。** Duhamel graph、simple diagram、recollision/crossing suppression 可借给
B4；它还展示怎样从 frozen coefficients 识别一个 collision operator。不能直接解除。

**不匹配。** `d=3`、weak disorder、harmonic、linear elastic scattering、Wigner weak
observable；冻结目标是 `O(1)` disorder、1D acoustic、nonlinear three-wave 和全模 `l1`。
论文明确排除 generic acoustic zero/band crossing。

### 6.2 Faou (2020) — 极限顺序不是技术细节

**来源与版本。** E. Faou,
[arXiv:1805.11269v3](https://arxiv.org/abs/1805.11269v3), 2020-04-21。
证据等级 **R**。

**精确模型。** 二维 bounded frequency domain 上的截断 KP-type quadratic system，
`omega(k)=k_x^3+eta k_y^2/k_x`；`O(N²)` Fourier modes，nonlinearity `epsilon`；可加入只作用
于 mode angles、保持 amplitudes/L2 的 Stratonovich noise `delta`。初始数据是 invariant
Gaussian / Rayleigh--Jeans law 的 `N^-alpha` variance perturbation，`1<=alpha<=2`，只研究
**linearized** kinetic equation与 coarse cells of mesh `h>>N^-1`。

**严格结论。** Theorem 1 在 `t<=T/(pi epsilon²)` 给 coarse-grained renormalized
second moments 与 broadened/linearized kinetic solution 的显式误差

```text
C [epsilon/(h delta²) + 1/(h delta N) + delta/N^(2-alpha)],
```

再令 `delta->0` 得 linearized WKE 的弱极限。Theorem 2 在**无噪声**、几乎每个 `eta`、
某 `beta>0` 下，若先取 `epsilon` 足够小相对 `N`，则同一时间窗

```text
sup_K |F_K^(N,h)(t)-g_0(K)|
 <= C [epsilon N^beta/h + 1/(hN)],
```

即 actions 由 Birkhoff reduction 近似冻结，没有非平凡 kinetic description。

**对 blocker。** 为 B4 提供“admissible joint limit 必须定量规定”的直接数学依据；
random initial phases 本身不保证 kinetic law。不能解除 B4。

**不匹配。** `d=2` KP dispersion、cutoff Fourier basis、near-RJ linearization、coarse weak
observable；目标没有 time-dependent noise，且 random mass eigenfrequencies/soft acoustic
edge 完全不同。

### 6.3 Staffilani--Tran (2024) — 最接近的 rigorous lattice three-wave full-time analogue

**来源与版本。** G. Staffilani, M.-B. Tran,
[arXiv:2106.09819v5](https://arxiv.org/abs/2106.09819v5), 2024-02-12。
证据等级 **R**。

**精确模型。** `d>=2` hypercubic periodic lattice 的 Zakharov--Kuznetsov finite-difference
system，quadratic nonlinearity `lambda`；

```text
omega(k)=sin(2 pi k_1) sum_j sin²(2 pi k_j),
bar_omega(k)=sin(2 pi k_1).
```

加入专门设计的 convolutive Stratonovich phase noise：它不改变 amplitudes/energy，主要
移除 ghost manifold 的 singular crossing。初态 mode variables 为独立 centered complex
Gaussians，profile 满足论文的 positivity/regularity 和 moment conditions。先取 lattice size
`D->infinity`，再研究 `lambda->0`。

**严格结论。** Theorem 3：写 `t=tau lambda^-2`，存在 `0<T_*<1`，对
`0<tau<T_*` 和每个固定 broadening `ell>0`，nonleading diagrams 在 Lebesgue measure 中
消失；修改后的 two-point function `f_ell` 在 measure 中收敛到 broadened three-wave
kinetic solution `f_ell^infinity`。论文明确指出未 broaden 的 Dirac resonance 在其 ZK
dispersion 上不定义为正测度。

**对 blocker。** full kinetic-time three-wave diagrammatics、leading/nonleading 分离和
resonance broadening 是 B4 的最佳架构来源；不直接解除 B4。

**不匹配。** `d>=2`、外加 time noise、translation-invariant Fourier modes、特定 ghost
manifold；不是 1D random masses、deterministic flow 或 full-mode late-window `l1`。

### 6.4 Deng--Hani (2023) — 真正 full kinetic time，但模型是 `d>=3` NLS four-wave

**来源与版本。** Y. Deng, Z. Hani,
[arXiv:2301.07063v2](https://arxiv.org/abs/2301.07063v2), 2023-03-20。
证据等级 **R**。

**精确假设。** `d>=3` continuum cubic NLS on a torus of side `L`（也覆盖任意 fixed
rectangular aspect ratios）；nonlinearity `alpha=L^-gamma` with `0<gamma<1`，
`T_kin=(2alpha²)^-1`。初始 Fourier modes 是 `sqrt(n_in(k)) g_k`，`n_in` 非负 Schwartz，
`g_k` iid normalized complex Gaussians（可扩展到 rotationally symmetric exponential-tail
laws）。

**严格结论。** Theorem 1.1：对依赖 `(d,gamma,n_in)` 的小 `delta>0`，以至少
`1-exp[-(log L)²]` 的概率，解存在到 `T=delta T_kin`，并且

```text
sup_{0<=t<=T} sup_k
| E |u_hat(t,k)|² - n(t/T_kin,k) | -> 0,
```

其中 `n` 解 four-wave WKE；论文还给 `L^-c` 级统一误差。

**对 blocker。** bad-vine cancellation、cutting algorithm、high-order diagram control 和
uniform trajectory comparison 可借给 B4；不直接解除。

**不匹配。** `d>=3`、homogeneous Fourier basis、four-wave NLS；没有 frozen disorder、
1D small-denominator/localization、acoustic zero 或全模 normalized `l1`。

### 6.5 Vassilev (2025) 与 Vassilev--Wu (2026) — 1D 的已知时间边界

**来源。** K. Vassilev,
[arXiv:2408.13693v2](https://arxiv.org/abs/2408.13693v2), 2025-11-12；
[Commun. Math. Phys. 406, 293](https://doi.org/10.1007/s00220-025-05455-7)。
K. Vassilev, B. Wu,
[arXiv:2605.19308v1](https://arxiv.org/abs/2605.19308v1), 2026-05-19。
证据等级 **R**。

**第一篇。** 1D MMT on length `L`，dispersion `|k|^sigma`，`0<sigma<=2`, `sigma!=1`，
nonlinearity `alpha=L^-gamma`，四波。WKE signal 被证明到
`L^-epsilon alpha^(-5/4)=L^-epsilon T_kin^(5/8)`；`1<sigma<=2` 时 proposed collision
kernel trivial，并证明二阶矩至 `T_kin` 没有非平凡动力学。

**第二篇。** equal-mass periodic **full beta-FPUT**，quartic nonlinearity
`beta=N^-gamma`；“full”表示 microscopic 方程保留 nonresonant terms。Theorem 1.1 的
时间为 `N^-epsilon min(N,N^(4gamma/3))`，最多 `T_kin^(2/3)`，识别二阶相关的第一
kinetic increment，而不是完整 WKE trajectory 或 equilibration hitting law。

**对 blocker。** 这两篇给 B4 的 1D diagram/resonance-counting 基线，并说明 1D 从
subkinetic 推到完整 kinetic time 仍是实质障碍；不解除 B4。

**不匹配。** 无 disorder；MMT/Fourier beta-FPUT 都是 four-wave；目标 cubic channel 是
three-wave，且 quartic stabilizer 的系数是 `O(g²)`，不能把 beta-FPUT 的四波时间直接
当成目标 `g^-2` 主过程。

## 7. 哪些文献结论可以进入 grounding DAG

一篇论文可以以以下三种方式进入 faithful grounding：

1. **external theorem record**：逐字记录 source theorem、版本、假设和结论；
2. **Lean hypothesis interface**：形式化“若目标对象满足 source-shaped 条件，则下游
   结论成立”；
3. **proved adapter**：在 Lean/伴随数学证明中证明 frozen target 确实满足这些条件。

只有第 3 步完成后才能解除 blocker。把 Wang 的 kinetic relation、Pezzi 的 H-theorem
或数值 slope 写成裸 `axiom`，最多得到 conditional theorem，不是 frozen v0.3 的
faithful proof。尤其不能把 `[N]` 证据升级为 `[R]`。

## 8. 最有希望的 theorem packages 与 Lean-ready 接口

以下是按依赖顺序而非容易程度排列的最小数学接口。名称是建议，不声称文献已经证明
目标实例。

### P1. 目标谐波算子的 acoustic/bulk spectral package

最先可落地的是把 Bernardin--Huveneers--Olla / Ajanki--Huveneers 的严格工具适配到
frozen periodic mass-weighted Jacobi operator：

```text
TargetHighModeEFC:
  E[sum_{k in I_N(alpha)} |psi_k(x) psi_k(y)|]
    <= C exp(-c |x-y|/N^(2 alpha)).

TargetAcousticCounting:
  # {k : 0 < omega_k <= eta} / N -> rho([0,eta])
  with quantitative probability error, uniformly along admissible eta=eta(N,g).

TargetSoftEnergyTightness:
  initial/kinetic energy carried by {omega<=eta} -> 0 as eta->0,
  uniformly in the required joint limit.
```

这只部分推进 B2，但可把“全非零模”问题严格分成 soft sector 与 bulk。

### P2. marked three-wave empirical collision measure — B1 的真正核心

定义每个 mode 的 mark 至少含 `(omega, localization_center, normalized_bond_leg)`，并定义

```text
nu_(N,g,T) = normalized sum over signed triples
  |V_123|² R_T(±omega_1 ±omega_2 ±omega_3)
  delta_(marks_1,marks_2,marks_3),
```

其中 `R_T` 是从有限时间 Duhamel 公式产生的 sinc-square / broadened kernel，而不是先验
塞入 Dirac delta。所需 theorem 接口应是：对一类 bounded-Lipschitz 且带 infrared
weight 的 tests `phi`，

```text
sup_phi |integral phi d nu_(N,g,T) - integral phi d nu| -> 0 in probability,
```

并给足以送入 micro remainder 的定量速率。这同时统一本地 scalar approximate-identity
结果、Wang 的 bond tensor 和随机谱 marks；任何只证明 IDS 的 theorem 都不够。

### P3. exact infrared compensation and collision connectivity

对 P2 得到的**同一个** limit kernel，证明：

```text
InfraredRateBounds:
  c w(omega) <= collision_frequency(omega) <= C w(omega)
  for an explicit degenerating weight w.

BulkCoercivity:
  DirichletForm(f) >= c_eta ||f-P_invariants f||² on {omega>=eta}.

CollisionInvariantClassification:
  every admissible invariant is generated only by target conserved quantities.

NetworkConnectivity:
  no positive-measure collision component thermalizes at an independent temperature.
```

Spohn 给 invariant-classification 逻辑，Germain--La--Menegaki 给 weighted/no-gap 逻辑；
二者的具体 dispersion、维数和 kernel 都必须重做。

### P4. target kinetic relaxation plus robust first crossing

接口不能只写“趋近平衡”，而应直接服务 frozen observable：

```text
TargetKineticRelaxation:
  global solution for the frozen initial basin;
  lateWindowL1(D,t) <= r(t),  r(t)->0;
  with soft-sector error included.

TransverseFirstCrossing:
  exists tau_*>0 and eta>0 such that
  distance >= delta+eta before tau_*-eta,
  and distance <= delta-eta on a post-crossing interval.
```

第二条才足以把 uniform observable convergence 转成 deterministic hitting-time limit。
Germain--La--Menegaki 只给不同 kernel 的近平衡 weighted decay，不给 frozen two-band basin
或该首达 margin。

### P5. deterministic random-mass micro-to-kinetic theorem

最终需要的 B4 接口强于通常单模二阶矩：对每个 fixed kinetic horizon `Tau`，

```text
sup_{0<=tau<=Tau}
  sum_{k=1}^{N-1}
  |E_k^micro(tau/g²) - E_k^kin(tau)| / totalEnergy
    -> 0 in probability,
```

或一个能严格推出同一 late-window normalized `l1` 的等价 empirical version。证明必须同时
处理：random eigenbasis、localized bulk、extended acoustic layer、nonresonant frequency
renormalization、quartic stabilizer 在 `g^-2` 时间的贡献，以及高阶 diagrams。

Faou 的 deterministic Birkhoff theorem 要求 joint-limit contract 明确排除“先让 `g` 比
finite-volume spacing 小太多”的冻结 actions regime。`N_min(g)` 应由 P2/P5 的误差估计
产生，不能预设一个未经证明的 `Ng` 或 `Ng²` 规则。

## 9. 最短可信研究路线

1. **先做 P1**：它最接近已有严格随机质量定理，并为全模 soft/bulk decomposition 给
   可复用事实；但它不会单独证明 thermalization。
2. **P2 是 B1 的关键新数学**：没有 marked collision measure，就没有“精确 kernel”，
   也无法诚实开始 B2/B3。
3. **P2 后并行做 P3 与目标 WKE 的 local/global theory**，再用 weighted relaxation
   证明 P4。
4. **P5 是最大风险和最终关键路径**。Staffilani--Tran 与 Deng--Hani 可提供 proof
   architecture，但 1D frozen disorder 并非小修改。
5. P4+P5 加已有 late-window / hitting-time Lean bridge，才能推出
   `g²T_eq -> tau_*`；若只做到 uniform tightness 和两个常数窗，则只能推出
   `Theta_P(g^-2)`，不能声称增强极限。

## 10. source/version 清单

| Source | 固定版本日期 | URL | 审计用途 |
|---|---:|---|---|
| Wang--Fu--Zhang--Zhao | 2019-07-24, v2 | https://arxiv.org/abs/1903.09502v2 | 目标邻近 F/N、有限顶点 |
| Pezzi et al. | 2021-03-12, v1 | https://arxiv.org/abs/2103.08336v1 | diatomic 三波几何 F/N |
| Dhar--Saito | 2008-06-25, v1 | https://arxiv.org/abs/0806.4067v1 | boundary-current N |
| McGinnis--Wright | 2023-08-11, v1 | https://arxiv.org/abs/2308.06115v1 | random FPUT KdV R |
| Bernardin--Huveneers--Olla | 2019-01-07, v2 | https://arxiv.org/abs/1710.08848v2 | random-mass EFC/hydrodynamics R |
| Ajanki--Huveneers | 2010-03-04, v1 | https://arxiv.org/abs/1003.1076v1 | transfer matrix / acoustic transport R |
| Bernard--Texier | 2026-02-04, v2 | https://arxiv.org/abs/2506.18693v2 | DOS/localization formula guidance |
| Huveneers | 2014-04-16, v5 | https://arxiv.org/abs/1203.3587v5 | weak-coupling nonresonance R |
| Huveneers--Lukkarinen | 2020-02-25, v1 | https://arxiv.org/abs/2002.10868v1 | prethermal normal form R/F/N |
| Spohn | 2005-09-01, v2 | https://arxiv.org/abs/math-ph/0505025v2 | three-phonon invariants/equilibria F/K |
| Bricmont--Kupiainen | 2007-03-02, v1 | https://arxiv.org/abs/math-ph/0703014v1 | kinetic relaxation K |
| Germain--La--Menegaki | 2024-09-03, v1 | https://arxiv.org/abs/2409.01507v1 | weighted FPU kinetic relaxation K |
| Lukkarinen--Spohn | 2005-05-27, v1 | https://arxiv.org/abs/math-ph/0505075v1 | weak-disorder linear kinetic R |
| Faou | 2020-04-21, v3 | https://arxiv.org/abs/1805.11269v3 | three-wave/order-of-limits R |
| Staffilani--Tran | 2024-02-12, v5 | https://arxiv.org/abs/2106.09819v5 | lattice three-wave full time R |
| Deng--Hani | 2023-03-20, v2 | https://arxiv.org/abs/2301.07063v2 | full kinetic diagrammatics R |
| Vassilev | 2025-11-12, v2 | https://arxiv.org/abs/2408.13693v2 | 1D subkinetic boundary R |
| Vassilev--Wu | 2026-05-19, v1 | https://arxiv.org/abs/2605.19308v1 | 1D full beta-FPUT, subkinetic R |

## 11. 最终审计结论

文献确实支持把 `g^-2` 作为 frozen v0.3 的**合理研究假说**：Wang 等给最邻近的物理
机制，Pezzi 等展示三波 resonance 可导致较快 thermalization，Staffilani--Tran 证明某些
lattice three-wave systems 在额外噪声和 `d>=2` 下确有 full kinetic limit。

但现有严格定理同时表明不可跳过的风险：random harmonic bulk localization、acoustic
edge 的退化、Faou 的极限顺序/Birkhoff regime、Huveneers 的任意阶 nonresonance、以及
1D full kinetic-time 图展开的现有边界。因而当前诚实状态仍是：**四个 blocker 全部开放；
论文可 grounding proof architecture，不能作为无条件公理把完整热化目标标记为已证。**
