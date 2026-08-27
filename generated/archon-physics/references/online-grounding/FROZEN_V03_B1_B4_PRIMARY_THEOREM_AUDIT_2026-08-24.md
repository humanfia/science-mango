# Frozen v0.3：B1--B4 一手文献定理级审计

日期：2026-08-24。

本文件只记录可核验的一手论文定理、假设映射和不可迁移边界。它不改变 frozen
source snapshot、主文献审计、DAG 状态或 release certificate，也不把论文结论作为
Lean 公理加入依赖图。

## 目标签名

需要同时覆盖的目标是：一维周期链、iid `Uniform[4/5,6/5]` 的 `O(1)` 随机质量、
势

`r^2/2 + (kappa*g/3) r^3 + (beta*g^2/4) r^4`,

iid Haar 初相、全部 `N-1` 正模、归一化 late-window energy `l1` observable，以及
`g^2 T_eq` 的高概率 tightness（增强目标为依概率收敛到常数）。

## B1/B2：随机谐波谱、projector 与低频

### Ajanki--Huveneers (2011)

O. Ajanki, W. Huveneers,
[*Rigorous scaling law for the heat current in disordered harmonic chain*](https://arxiv.org/abs/1003.1076),
Commun. Math. Phys. 301 (2011),
[DOI](https://doi.org/10.1007/s00220-010-1161-1).

- 论文的 iid 正质量假设允许密度在紧支撑内部为 `C^1` 且导数有界；因此精确的
  `Uniform[4/5,6/5]` 可以覆盖，不需要把端点 mollify。
- Eq. (2.2) 的二乘二递推与本地
  `u_(j+1) = (2-m_j*Omega^2)u_j-u_(j-1)` 相同，只差论文的无量纲频率重标度。
- Eq. (4.2) 严格给出低频 Lyapunov exponent
  `gamma(w) = pi^2 E[B^2] w^2/8 + O(w^3)`。冻结分布满足
  `E[m]=1`、`Var(m)=1/75`，换回物理频率后得到
  `gamma_phys(Omega)=Omega^2/600+O(Omega^3)`。
- 定理的主结论是带热浴、固定边界链的平均热流标度，不是有限周期本征投影、三波
  marked empirical measure 或非线性热化。合法的 Lean 接口必须先固定非零频率，再
  陈述随机乘积极限；不能无证明地交换“所有实频率”和满测集量词。

### Bernardin--Huveneers--Olla (2019)

C. Bernardin, F. Huveneers, S. Olla,
[*Hydrodynamic limit for a disordered harmonic chain*](https://arxiv.org/abs/1710.08848),
Commun. Math. Phys. 365 (2019),
[DOI](https://doi.org/10.1007/s00220-018-3251-4).

- Eq. (5.1) 的质量加权谐波算子正是 `M^(-1/2)(-Delta)M^(-1/2)`，与本地
  `harmonicHermitian` 相同。
- Section 5.3 给高模 eigenfunction-correlator：对指定高模窗，期望的
  `sum_k |psi_x^k psi_y^k|` 在尺度 `N^(2 alpha)` 上指数衰减；Lemma 3 还给高概率的
  有限体积局域区间。
- 正文证明展示的是 free boundary。作者说 fixed/periodic 也可处理，但这句话不是周期
  版本的定理。论文通常采用紧支撑光滑密度；精确 box-uniform 与周期边界都还需要重证
  适配。因此该结果不能直接实例化 frozen projector kernel。
- harmonic normal-mode energy 在该模型中逐模守恒；论文不能作为 nonlinear
  thermalization 的依据。

### Matsuda--Ishii (1970)

H. Matsuda, K. Ishii,
[*Localization of Normal Modes and Energy Transport in the Disordered Harmonic Chain*](https://doi.org/10.1143/PTPS.45.56),
Prog. Theor. Phys. Suppl. 45 (1970).

- Eq. (2.1) 与本地 generalized eigen-equation 相同；对每个固定非零频率，论文验证
  Furstenberg 条件并得到随机 transfer product 的正指数增长。
- 低频二次系数与 Ajanki--Huveneers 的现代归一化一致，冻结参数下为 `1/600`。
- 原文明确把无限链指数增长到大有限链正规模局域化的跳步称为 `IF-assumption`。因此
  不能用该论文宣布 frozen finite periodic eigenprojector localization。

### Pastur 与周期 IDS bridge

L. A. Pastur,
[*Spectra of random selfadjoint operators*](https://www.mathnet.ru/eng/rm4834),
Russian Math. Surveys 28 (1973).

- 经典定理给 metrically transitive 随机算子的非随机、自平均 eigenvalue-counting
  limit，但目标 acoustic Jacobi family 仍需逐项验证平移协变、ergodicity 与有限体积
  trace bridge。
- path 与 cycle 的 wrap edge 是一个 rank-one 二次型修正，足以期待 normalized
  eigenvalue count 相差至多 `1/N`；它不能转移 eigenfunction-correlator 或 projector
  衰减。
- 本地逐序比较
  `(5/6) lambda_clean(k) <= lambda_random(k) <= (5/4) lambda_clean(k)`
  已经允许在不导入 IDS 定理的情况下证明逐样本 threshold-count envelope。

### 不可作为定理借入的周期低频公式

U. M. Titulaer, J. M. Deutch,
[*Low-frequency behavior of a one-dimensional harmonic random lattice*](https://web.mit.edu/chemistry/deutch/technical/pdf10/102PhysRev24Gp4329%281981%29.pdf),
Phys. Rev. B 24 (1981).

论文的有限维 resolvent residue 公式可作为谱分解的推导指南；但其低频 averaged-density
展开依赖作者明确声明未证明、只在低阶检验的多项式根假设，不能进入 faithful theorem
DAG。

## B3/B4：kinetic operator、微观极限与弛豫

### Vassilev--Wu (2026)

K. D. Vassilev, B. Wu,
[*Rigorous Derivation of the Wave Kinetic Equation for full beta-FPUT System*](https://arxiv.org/abs/2605.19308),
arXiv:2605.19308.

- Theorem 1.1 处理等质量、周期、纯 beta-FPUT；随机性来自 Gaussian 或 Haar Fourier
  初值，不来自质量。
- 论文联立取 `beta=N^(-gamma)`，kinetic time 为 `beta^(-2)`，但证明时间严格短于完整
  kinetic time；结论是二阶矩的 subkinetic 一阶展开，不是 WKE trajectory 的完整时间
  收敛或长期平衡。
- 冻结目标的 quartic 系数是 `O(g^2)`，单独映射该通道会给 `g^(-4)`；目标的
  `g^(-2)` 来自 cubic 三波通道。因此该定理不能实例化 B4。

### Lukkarinen--Spohn (2007)

J. Lukkarinen, H. Spohn,
[*Kinetic Limit for Wave Propagation in a Random Medium*](https://arxiv.org/abs/math-ph/0505075),
Arch. Ration. Mech. Anal. 181 (2007).

- Theorem 2.3 是无限三维、pinned harmonic lattice、`sqrt(epsilon)` 弱质量无序的
  disorder-averaged Wigner limit，得到线性 Boltzmann 方程。
- 论文不覆盖一维 acoustic、`O(1)` 无序、anharmonicity 或样本级 self-averaging；碰撞
  机制也是弹性无序散射，不是三波热化。只能借 diagram/re-collision 的组织方式。

### Vassilev--Wu 之外的严格 microscopic 结果

J. Lukkarinen, H. Spohn,
[*Weakly nonlinear Schrödinger equation with random initial data*](https://arxiv.org/abs/0901.3283),
Invent. Math. 183 (2011)，处理 `d>=4` 离散 NLS 的平衡 covariance damping；维数、
方程、初态和 observable 均不匹配。

G. Staffilani, M.-B. Tran,
[*On the wave turbulence theory for a stochastic KdV type equation*](https://arxiv.org/abs/2106.09819),
处理 `d>=2` stochastic ZK，并保留外部相位噪声和固定 resonance broadening；不能作为
无噪声 random-mass FPUT 的 exact-resonance limit。

W. De Roeck, F. Huveneers, O. A. Prośniak,
[*Long Persistence of Localization in a Disordered Anharmonic Chain Beyond the Atomic Limit*](https://arxiv.org/abs/2308.11243),
Commun. Math. Phys. 406 (2025)，证明 pinned disordered Klein--Gordon 链的局域化在任意
多项式弱非线性时标上持续。模型不直接反驳 acoustic random-mass FPUT，但严格警告不能
仅从一维无序和形式三波共振推断 `g^(-2)` 热化。

### 已有 kinetic 方程自身的弛豫结果

P. Germain, J. La, A. Menegaki,
[*Stability of Rayleigh--Jeans equilibria in the kinetic FPU equation*](https://arxiv.org/abs/2409.01507),
研究等质量 beta-FPUT 的四波 kinetic equation。其线性化算子无 spectral gap，只在
nonsingular Rayleigh--Jeans 平衡的小邻域证明带权多项式弛豫；不能用于随机质量三波
kernel 或两带远离平衡数据。

J. Lukkarinen, H. Spohn,
[*Anomalous energy transport in the FPU-beta chain*](https://arxiv.org/abs/0704.1607),
严格分析的是等质量四波线性化 collision operator；microscopic kinetic scaling 在论文中
明确仍是 conjecture。

J. Bricmont, A. Kupiainen,
[*Approach to equilibrium for the phonon Boltzmann equation*](https://arxiv.org/abs/math-ph/0703014),
证明的是一个 `d>=2`、pinned、修改色散的四声子 Boltzmann 方程在平衡附近的弛豫，
不是 microscopic derivation，也不覆盖一维 acoustic kernel。

G. Staffilani, M.-B. Tran,
[*Entropy Structures and Long-Time Relaxation for 3-Wave Kinetic Equations*](https://arxiv.org/abs/2605.10788),
给频率空间三波方程的 entropy 与长时 cascade；其局部极限为零表示能量流向无限频率，
不是有限模态 equipartition。

L. Migliorelli, G. Dematteis, S. Chibbaro, M. Onorato,
[*Resonant interactions in the alpha-FPUT lattice with site-dependent coefficients*](https://arxiv.org/abs/2605.24268),
形式上推导弱 site-modulation 的三波 kinetic equation，但作者明确不声称 fully rigorous
microscopic derivation；模型也不是 `O(1)` iid random masses。

## 本地形式化裁决

可以无新增公理落地的部分：

1. 有限 transfer/monodromy 与谱多项式恒等式；
2. 逐序 random/clean 谱比较及 threshold-count 包含关系；
3. 单 triad 和有限 collision network 的能量守恒、H-theorem 与 equality algebra；
4. summed interaction moment 到 weighted spectral-projector kernels 的精确有限因子化；
5. projector-weighted resolvent 的有限维谱展开。

不能直接作为 frozen 定理借入的部分：

1. random-mass marked triple empirical measure 的联合极限；
2. finite periodic exact-uniform projector/EFC 衰减；
3. 目标 sample-specific 三波 kernel 的 infrared 双边界、connectivity 与 coercivity；
4. `t~g^(-2)` 上 microscopic observable 到 kinetic trajectory 的完整余项控制；
5. expectation/Wigner 结论升级为样本高概率 late-window `l1` hitting law。

因此文献可以缩短证明链、确定正确接口和常数，但目前没有一篇论文能作为 B1--B4 中
任一主节点的直接 replacement theorem。
