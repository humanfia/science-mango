# Deng–Hani：从 cubic NLS 严格推导波动理学方程

本文整理并审计以下论文的核心内容、证明结构、适用边界，以及它对随机质量 LJ/FPUT 热化研究路线的启发。

> Yu Deng and Zaher Hani, “Full derivation of the wave kinetic equation”, Inventiones Mathematicae 233 (2023), no. 2, 543–724.

- DOI：https://doi.org/10.1007/s00222-023-01189-2
- arXiv：https://arxiv.org/abs/2104.11204
- Zbl：Zbl 1530.35276
- 本文审计日期：2026-08-27

## 1. 核心结论

这篇论文没有把 wave kinetic equation（WKE）当作假设，而是从大环面上的 cubic nonlinear Schrödinger equation（NLS）出发，在弱非线性与热力学联合极限下，严格推出模态二阶矩由四波 WKE 描述。

证明链是

\[
\text{Hamiltonian NLS}
\longrightarrow
\text{Fourier–Duhamel 图展开}
\longrightarrow
\text{规则图重求和与异常图压低}
\longrightarrow
\text{四波 WKE}.
\]

因此，这篇论文是本项目“从微观 Hamiltonian 出发，而不是承认 kinetic equation”的主要方法模板。

需要同时保留三个边界：

1. 初始 Fourier 模态是经过准备的随机独立模态，不是任意确定性初态。
2. 论文证明的是 NLS 二阶统计量趋于 WKE，不是 WKE 必然趋于热平衡。
3. 证明本质上使用弱非线性极限，不能直接推出任意强相互作用下的 kinetic equation。

## 2. 微观系统：Hamiltonian cubic NLS

论文考虑 \(d\ge 3\) 时大环面上的 cubic NLS：

\[
(i\partial_t-\Delta_\beta)u+\lambda^2|u|^2u=0,
\qquad x\in\mathbb T_L^d.
\]

这里 \(\Delta_\beta\) 是由环面长宽比 \(\beta\) 决定的 twisted Laplacian。论文的主要版本要求 \(\beta\) 位于一个明确 Lebesgue 零测集之外，即采用泛型非有理环面。

NLS 是 Hamiltonian 场方程。虽然方程中的非线性 \(|u|^2u\) 对 \(u\) 是三次的，但相互作用 Hamiltonian 对场是四次的。因此对应的是

\[
2\leftrightarrow2
\]

四波碰撞，而不是三波碰撞。

论文首先通过 gauge/Wick 重整化去掉只产生整体非线性相位漂移的平凡共振：

\[
|u|^2u
\quad\rightsquigarrow\quad
|u|^2u-2\fint |u|^2\,u.
\]

这一步不会改变模态能量交换，却把平凡 self-energy 相位从真正的碰撞动力学中分离出来。对 LJ/FPUT 的迁移中，非线性频率漂移也必须以类似方式单独重整化。

## 3. 初始随机系综

初始 Fourier 系数取为

\[
\widehat u_{\mathrm{in}}(k)
=\sqrt{n_{\mathrm{in}}(k)}\,\eta_k,
\qquad k\in L^{-1}\mathbb Z^d,
\]

其中：

- \(n_{\mathrm{in}}\colon\mathbb R^d\to[0,\infty)\) 是非负 Schwartz 函数；
- \(\eta_k\) 相互独立；
- 正文证明采用标准中心复 Gaussian；
- 论文说明单位圆上的均匀随机相位也可作类似处理。

因此

\[
\mathbb E|\widehat u_{\mathrm{in}}(k)|^2=n_{\mathrm{in}}(k).
\]

这里随机相位只在初始时刻作为概率模型输入。论文没有在正时间重新假设 RPA 或 Gaussian closure，而是直接控制由精确 NLS 动力学产生的图展开。

需要注意：这仍然不是“从任意确定性相位自发产生随机相位”的定理。正时间的传播混沌和更高阶统计由后续论文进一步研究：

- https://arxiv.org/abs/2110.04565

## 4. 弱非线性与热力学联合极限

按论文采用的 Fourier 归一化，有效非线性强度定义为

\[
\alpha:=\lambda^2L^{-d}.
\]

主定理选择

\[
\lambda=L^{(d-1)/2},
\qquad
\alpha=L^{-1}.
\]

因此 kinetic time 是

\[
T_{\mathrm{kin}}
:=\frac{1}{2\alpha^2}
=\frac{L^2}{2}.
\]

这说明真正趋于零的小参数是有效非线性 \(\alpha\)，而不是方程表面出现的 \(\lambda\)。热力学极限和弱非线性极限按照

\[
L\to\infty,
\qquad
\alpha L=1
\]

同步进行。

## 5. 被推导出的四波 WKE

极限模态密度 \(n(\tau,k)\) 满足齐次四波 WKE：

\[
\partial_\tau n(\tau,k)=\mathcal K(n,n,n)(k),
\qquad
n(0,k)=n_{\mathrm{in}}(k).
\]

碰撞算子为

\[
\begin{aligned}
\mathcal K(\phi_1,\phi_2,\phi_3)(k)
=\int_{\left(\mathbb R^d\right)^3}
&\big[
\phi_1(k_1)\phi_2(k_2)\phi_3(k_3)
-\phi_1(k)\phi_2(k_2)\phi_3(k_3)\\
&+\phi_1(k_1)\phi_2(k)\phi_3(k_3)
-\phi_1(k_1)\phi_2(k_2)\phi_3(k)
\big]\\
&\times
\delta(k_1-k_2+k_3-k)\\
&\times
\delta\!\left(
|k_1|_\beta^2-|k_2|_\beta^2
+|k_3|_\beta^2-|k|_\beta^2
\right)
\,dk_1\,dk_2\,dk_3.
\end{aligned}
\]

两个 Dirac delta 分别来自：

1. NLS Fourier 顶点的动量守恒；
2. kinetic time 极限下振荡时间积分产生的频率共振。

所以碰撞核是微观 Fourier 动力学和连续极限的结论，而不是外部输入。

## 6. 2023 年主定理的精确内容

固定：

- \(d\ge3\)；
- 泛型环面参数 \(\beta\)；
- \(A\ge40d\)；
- 非负 Schwartz 初始谱 \(n_{\mathrm{in}}\)；
- 足够小、但与 \(L\) 无关的 \(\delta>0\)。

当

\[
\alpha=L^{-1},
\qquad
T_{\mathrm{kin}}=\frac{L^2}{2},
\]

且 \(L\) 足够大时，论文证明：

1. NLS 以至少

   \[
   1-L^{-A}
   \]

   的概率在

   \[
   0\le t\le\delta T_{\mathrm{kin}}
   \]

   上存在光滑解。

2. 模态二阶矩一致收敛：

   \[
   \lim_{L\to\infty}
   \sup_{\tau\in[0,\delta]}
   \sup_{k\in L^{-1}\mathbb Z^d}
   \left|
   \mathbb E|\widehat u(\tau T_{\mathrm{kin}},k)|^2
   -n(\tau,k)
   \right|
   =0.
   \]

3. 收敛是定量的：存在 \(\nu=\nu(d)>0\)，使误差满足

   \[
   \sup_{\tau\in[0,\delta]}
   \sup_k
   \left|
   \mathbb E|\widehat u(\tau T_{\mathrm{kin}},k)|^2
   -n(\tau,k)
   \right|
   \le C L^{-\nu}.
   \]

这里证明的是 ensemble-averaged mode energy。它本身不是每个单独随机样本的经验谱逐路径收敛定理。

## 7. 证明机制

### 7.1 Fourier interaction representation

去掉线性流并把物理时间缩放到 \([0,1]\) 后，模态变量 \(a_k(t)\) 满足带快速振荡相位的精确方程：

\[
\partial_t a_k
\sim
\frac{\delta}{L^{d-1}}
\sum_{k_1-k_2+k_3=k}
e^{\,i\delta L^2\Omega t}
a_{k_1}\overline{a_{k_2}}a_{k_3},
\]

其中

\[
\Omega
=|k_1|_\beta^2-|k_2|_\beta^2
+|k_3|_\beta^2-|k|_\beta^2.
\]

### 7.2 深度为 \(\log L\) 的 Duhamel 展开

论文将解展开为

\[
a_k
=\sum_{n=0}^{N_{\mathrm{exp}}}\mathcal J_n+b_k,
\qquad
N_{\mathrm{exp}}=\lfloor\log L\rfloor.
\]

在 kinetic critical time 上，每增加一阶只能获得大约 \(\sqrt\delta\) 的小量。因此展开深度必须随 \(L\) 増长，不能停在固定有限阶。

### 7.3 Gaussian Wick 配对与 couples

每个 Duhamel 项由 ternary tree 表示。计算

\[
\mathbb E\!\left[
\mathcal J_{n_1}\overline{\mathcal J_{n_2}}
\right]
\]

时，初始 Gaussian 的 Wick/Isserlis 公式把叶子两两配对，形成 pairs of trees，论文称为 couples。

树的数量只有指数增长，但叶子配对的数量具有阶乘增长。这是 kinetic critical time 上的核心组合困难。

### 7.4 regular 与 dominant couples

regular couples 是能够达到最坏估计、因而不会自动得到额外 \(L\) 衰减的图。

其中：

- dominant couples 给出真正的 WKE 主项；
- non-dominant regular couples 的连续极限系数发生抵消；
- 所有 dominant regular couples 必须按任意阶重求和。

论文证明偶数阶微观图的总和与 WKE 相应 Taylor 系数一致；奇数阶主项消失。也就是说，完整 WKE 来自所有规则重复碰撞，而不是只保留一次 Fermi-golden-rule 碰撞。

### 7.5 irregular chains 的成组抵消

某些 irregular chains 单独估计时可能过大，甚至失去预期的 \(\delta^n\) 小量。

论文将 congruent irregular chains 成组，并利用：

- 共振相位的对应关系；
- 输入谱之间的小平移；
- 图符号的相反性；

得到精确或定量抵消。

所以不能把这些图逐个宣布为小量；小量来自图族之间的相消。

### 7.6 molecule reduction 与共振格点计数

去掉 regular sub-couples 和 irregular chains 后，论文把剩余组合结构转成 molecule 图。

每个 molecule atom 编码一个四波约束：

\[
a-b+c-d=0,
\]

\[
|a|_\beta^2-|b|_\beta^2
+|c|_\beta^2-|d|_\beta^2
\approx\text{给定值}.
\]

通过 molecule reduction algorithm、格点计数和 circle method，非规则结构按其偏离 regular couples 的指数 \(r\) 获得

\[
L^{-\nu r}
\]

增益。这个增益抵消了图数目的阶乘增长。

### 7.7 remainder 控制

截断余项满足一个含随机线性算子 \(\mathcal L\) 的方程。论文没有要求 \(\mathcal L\) 在某个单步范数中必然是压缩，而是控制 \(\mathcal L^n\) 和其谱半径，从而构造

\[
(1-\mathcal L)^{-1}.
\]

最后结合 Gaussian hypercontractivity 和高概率估计，完成精确 NLS 解与图展开、再与 WKE Taylor 展开的比较。

## 8. 论文证明了什么、没有证明什么

### 论文已经证明

- 从 Hamiltonian cubic NLS 推导四波 WKE；
- 在 kinetic timescale 的固定小比例上实现定量逼近；
- 规则高阶图重求和为 WKE；
- 非规则图通过计数增益或成组抵消被压低；
- WKE 碰撞核由微观动量与能量共振产生。

### 这篇 2023 论文没有证明

- 任意确定性初态自动产生随机相位；
- 单个有限系统的所有模态逐路径服从确定性 WKE；
- WKE 一定收敛到 Rayleigh–Jeans 或能量均分平衡；
- NLS 的无条件完整热化；
- 固定有限 \(L\) 后的无穷时间热平衡；
- \(O(1)\) 强相互作用下的 kinetic equation；
- 随机质量 LJ/FPUT 的 phonon WKE。

### 后续工作

- 传播混沌与高阶统计：https://arxiv.org/abs/2110.04565
- 完整 scaling range：https://arxiv.org/abs/2301.07063
- 覆盖 WKE 完整存在寿命的长时间推导：https://arxiv.org/abs/2311.10082

后续论文中的“任意长 kinetic 时间”是指覆盖给定 WKE 解的完整存在寿命，不等于对固定有限微观系统证明 \(t\to\infty\) 后永远热平衡。

## 9. 对随机质量 LJ/FPUT 的迁移字典

| Deng–Hani cubic NLS | 随机质量 LJ/FPUT |
|---|---|
| Fourier 模态 \(k\) | 质量加权随机正常模 \(j\) |
| 色散 \(|k|_\beta^2\) | 随机本征频率 \(\omega_j\) |
| 精确 Fourier 动量守恒 | 样本相关的模态相互作用张量 |
| 常系数四波顶点 | 三波、四波及更高的随机顶点 |
| Gaussian Fourier 初值 | 给定质量环境后的 circular Gaussian 正常模初值 |
| circle-method 格点计数 | quenched 随机谱小球估计与共振测度收敛 |
| 规则图 | 规则三波/四波碰撞历史 |
| generic torus 的算术非退化 | 正质量随机谱、局域长度与模态重叠非退化 |
| WKE 是定理结论 | phonon kinetic equation 也必须是结论 |

最重要的差别是：随机质量链不再具有 Fourier 动量标签。若

\[
A_m u_j=\omega_j^2u_j
\]

是质量加权谐性算子的本征系统，则三波顶点具有类似

\[
V_{j_1j_2j_3}^{(3)}
\sim
\sum_x
b_{xj_1}b_{xj_2}b_{xj_3}
\]

的形式，其中 \(b_{xj}\) 是本征模在 bond 上的梯度分量。

频率 \(\omega_j\)、本征矢 \(u_j\) 和顶点 \(V^{(3)}\) 来自同一个质量环境，彼此高度相关。只证明随机频率变稠密并不够，还必须证明近共振模态具有足够的空间重叠。

## 10. 随机质量 LJ/FPUT 的正确顶层定理

目标不能写成“假设 kinetic approximation 成立”。正确结构应是：

\[
\text{正质量随机 Hamiltonian}
\Longrightarrow
\text{随机正常模与顶点}
\Longrightarrow
\text{加权近共振测度}
\Longrightarrow
\text{phonon WKE}.
\]

候选 quenched 定理应具有如下语义。对几乎每个无限质量环境 \(m\)，取其前 \(N\) 个质量构成有限链；给定 \(m\) 后，以独立 circular complex Gaussian 生成初始正常模。证明存在由真实本征频率和真实顶点导出的确定性碰撞测度 \(\Gamma_{\mathrm{res}}\)，使

\[
\sup_{0\le\tau\le\delta}
d\!\left(
\mathbb E_\eta\mu^m_{N,g}(\tau g^{-2}),
\mu(\tau)
\right)
\longrightarrow0.
\]

这里：

- \(\mu^m_{N,g}\) 是精确有限 Hamiltonian 流的经验模态能量测度；
- \(\Gamma_{\mathrm{res}}\) 必须由微观谱和顶点极限得到；
- \(\mu(\tau)\) 满足由 \(\Gamma_{\mathrm{res}}\) 定义的 kinetic equation；
- positive-time RPA、碰撞核非零和 kinetic approximation 都不能列为前提。

若三波碰撞测度严格非零且碰撞网络连通，则三波 kinetic time 是 \(g^{-2}\)。在低能量 LJ 的自然缩放中 \(g\propto\sqrt e\)，候选热化律因此是

\[
T_c\sim e^{-1}.
\]

若三波核因为对称性、运动学或局域化而退化，则必须进入四波或更高阶尺度；此时不能预设 \(-2\) 指数。

## 11. 迁移证明的主要缺口

### 11.1 正质量概率模型

未经截断的 Gaussian 质量会以正概率产生非正质量。在无限 iid 链中，“所有质量均为正”的概率为零。因此严格模型应使用：

- 支撑在 \([m_-,m_+]\subset(0,\infty)\) 的截断 Gaussian；
- 或其他严格正且具有足够正则性的概率分布。

### 11.2 quenched 加权共振测度

必须证明有限时间展宽核加权的共振和存在极限，例如三波情形中的

\[
\frac1N
\sum_{j_1,j_2,j_3}
|V^{(3)}_{j_1j_2j_3}|^2
\delta_t(\omega_{j_1}-\omega_{j_2}-\omega_{j_3}),
\]

其中

\[
\delta_t(\Omega)
=\frac{t}{2\pi}
\operatorname{sinc}^2\!\left(\frac{t\Omega}{2}\right).
\]

该极限必须同时控制：

- 小分母统计；
- 本征模局域中心；
- bond-leg overlap；
- 频率与顶点的共同环境依赖；
- 有限尺寸到热力学极限的 uniform integrability。

### 11.3 一维局域化

固定强度的一维 iid 质量无序通常引入模态局域化。它可能增加频率近共振，却同时压低远距离模态顶点。

因此碰撞核是否非零必须成为定理结论。若严格计算发现极限碰撞测度退化，正确结果应是：

- \(g^{-2}\) 时间上只有自由传播或频率重整化；
- 改用更长碰撞时间；
- 或采用弱无序与弱非线性的联合极限。

不能把“碰撞核非零”作为公理补进 grounding DAG。

### 11.4 Hamiltonian remainder

需要像 Deng–Hani 一样证明：

- 规则图重求和为候选 kinetic 方程；
- 非规则图得到 \(N\) 一致衰减或成组抵消；
- 图展开 remainder 在完整 kinetic window 上趋零；
- 正时间 connected cumulants 与 anomalous correlations 得到控制。

这是一维随机质量 LJ/FPUT 当前最困难的微观到动理学部分。

### 11.5 LJ 到低阶 FPUT 的动力学转移

LJ 的局部 Taylor 展开本身不足以证明 kinetic time 上两条 Hamiltonian 轨道接近。必须另证：

- kinetic time 内不会接近 LJ 奇点或发生键解离；
- Taylor remainder 的长期累积仍然可控；
- exact LJ 与其 FPUT 正规形在模态能量统计上具有 kinetic-window universality。

## 12. 重构后的研究 DAG

\[
\boxed{\text{F1：Hamiltonian 谱与共振几何}}
\longrightarrow
\boxed{\text{F2：微观图展开与 kinetic 极限}}
\longrightarrow
\boxed{\text{F3：kinetic 松弛}}
\longrightarrow
\boxed{\text{F4：回拉到微观热化}}
\]

### F1：Hamiltonian、随机谱与顶点

- 正质量随机环境；
- 有限链 Hamiltonian 全局流；
- 质量加权正常模；
- 三波、四波顶点；
- 局域长度与模态 overlap；
- broadened on-shell collision measure。

### F2：微观到 kinetic

- 初始 Gaussian Wick 结构；
- Duhamel trees/couples；
- regular collision histories 的重求和；
- nonregular diagrams、irregular chains 和 recollisions 的压低；
- positive-time propagation of chaos；
- remainder 的完整 kinetic-time 控制。

### F3：kinetic 方程的热化

- 解的适定性；
- 守恒量与平衡态；
- H-theorem；
- 碰撞网络连通性；
- coercivity 或无谱隙时的多项式松弛；
- 热化阈值的 hitting-time 标度。

### F4：回拉与极限顺序

- kinetic 解与微观能量均分误差的稳定传递；
- 有限尺寸残差；
- \(N\to\infty\) 后的严格均分；
- 在 WKE 有效寿命内的持续性；
- 区分有限系统 Poincaré recurrence 与热力学极限。

## 13. 与现有 archon-physics 形式化的关系

现有 quantitative RPA、history-aware certificate 和 two-sided hitting-time 模块仍然有用，但它们只能作为 F2/F3 之后的下游消费者。

它们已经形式化的内容是：

- 如果微观耗散与 kinetic 耗散之间存在定量相对误差，则可得双边耗散界；
- 如果熵缺陷满足双边微分不等式，则可得 \(T_c\) 的双边标度；
- 有限观测残差可以进入热化阈值界。

它们尚未证明：

- 随机质量 LJ/FPUT 自动满足 RPA；
- 碰撞核由微观谱极限产生且非零；
- 微观 Hamiltonian 在完整 kinetic time 上趋于该 kinetic 方程。

因此这些模块不能被表述为完整微观热化证明，而应作为 Deng–Hani 型微观推导成功后的严格下游接口。

## 14. 证据等级

为防止把研究目标误写成已证明定理，后续文档和 Lean 模块应统一采用以下标签：

- 已由 Deng–Hani 2023 证明：cubic NLS 在指定联合极限下的二阶矩趋于四波 WKE。
- 已由后续论文证明：传播混沌、完整 scaling range，以及覆盖 WKE 存在寿命的长时间版本。
- 本项目已形式化的条件接口：定量 RPA 缺陷、history-aware 耗散比较、双边热化时间界。
- 尚待证明：一维随机质量 LJ/FPUT 的 quenched 共振测度、完整微观到 kinetic 极限、LJ kinetic-window universality 和由此得到的热化律。

## 15. 最终判断

Deng–Hani 的工作证明了一个关键原则：

\[
\text{kinetic equation 可以从 Hamiltonian 波动方程严格导出。}
\]

但可迁移的是证明架构，不是现成的 NLS 碰撞核。对随机质量 LJ/FPUT，真正的核心任务是以

\[
\text{随机谱统计}
+\text{模态空间重叠}
+\text{历史感知图抵消}
\]

替代 NLS 中的 Fourier 动量守恒、circle method 和泛型环面格点计数。

只要这一微观层完成，现有的 kinetic 松弛与热化时间形式化就能作为后端使用；在此之前，不能把条件式结果称为随机质量 LJ/FPUT 的完整热化证明。
