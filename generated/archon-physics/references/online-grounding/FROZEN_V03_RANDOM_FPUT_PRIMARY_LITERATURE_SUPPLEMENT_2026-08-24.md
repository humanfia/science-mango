# Frozen v0.3 随机质量 FPUT：补充一手文献核验

本文件补充主审计之后检索到的来源；它不改变 frozen campaign source snapshot、DAG
状态或 release certificate。

## Fu--Zhang--Zhao (2021)：压力下随机质量 FPUT-beta 的数值平方律

W. Fu, Y. Zhang, H. Zhao,
[arXiv:2105.14855v1](https://arxiv.org/abs/2105.14855v1)；
[Phys. Rev. E 104, L032104](https://doi.org/10.1103/PhysRevE.104.L032104)。

作者比较有压力/应变的单原子链与 mass-disordered FPUT-beta 链，数值上观察到热化时间
与其定义的 nonintegrability strength 平方成反比。这是 `g^-2` 现象的独立数值支持，
但不是概率 tightness、微观到 kinetic 极限或首达时间定理。其模型也不是 frozen
cubic-leading 势、Haar 初态或全 `N-1` 模 late-window `l1` observable。因此它不能加入
无公理 release DAG 的 theorem 依赖边，也不解除 B1--B4。

## Matsuda--Ishii (1970)：transfer-matrix 局域化结果的精确边界

H. Matsuda, K. Ishii,
[*Localization of Normal Modes and Energy Transport in the Disordered Harmonic Chain*](https://doi.org/10.1143/PTPS.45.56),
Prog. Theor. Phys. Suppl. 45, 56--86 (1970)。

对一维 isotopically disordered infinite harmonic chain，论文证明固定频率差分方程的
transfer-matrix 解几乎必然具有指数增长率，并计算低频增长率。这支持把 acoustic edge
与 bulk 分开并用 Lyapunov exponent 组织 B2。

论文也明确指出，从“修改一个质量后可构造局域解”并不能逻辑上推出任意给定大有限样本
的几乎所有正规模都相应局域。该结果不涉及 anharmonic 三波碰撞、marked overlap 经验
极限或热化，不能被提升成 frozen finite-cycle projector/localization theorem，也不解除
B1--B4。


## Migliorelli--Dematteis--Chibbaro--Onorato (2026)：空间调制产生低阶共振

L. Migliorelli, G. Dematteis, S. Chibbaro, M. Onorato,
[*Resonant interactions in the alpha-FPUT lattice with site-dependent coefficients*](https://arxiv.org/abs/2605.24268v1),
arXiv:2605.24268v1 (2026-05-22)。

论文研究齐质量、弱位点依赖弹簧刚度与非线性系数的 alpha-FPUT 链。其 Fourier
推导显示空间调制可以产生常系数模型中不存在的低阶共振，并形式上得到含 Bragg
scattering 与 three-wave+1 collision 项的 kinetic equation；非线性碰撞项带小参数平方，
因此预测 `epsilon^-2` 能量转移时标。

这为 frozen cubic-leading 随机链的 `g^-2` 机制提供了比齐次 beta-FPUT 更接近的物理
grounding，也给出可迁移的局部三波能量守恒与 H-theorem 代数。但是作者明确说明没有
给出 fully rigorous microscopic-to-kinetic derivation。其无序是相对齐次刚度的弱空间调制，
线性模仍用确定性 Fourier 色散；它不是 `[4/5,6/5]` 的 `O(1)` iid 随机质量模型，也没有
证明随机 eigenfrequency/eigenvector marked empirical limit、完整 kinetic-time remainder、
collision connectivity 或 frozen late-window hitting law。因此不能解除 B1--B4，也不会被
作为公理加入 release DAG。


## Bernard--Texier (2026)：精确谱行列式与近似低频渐近的分界

M. Bernard, C. Texier, [*Disordered harmonic chains with random masses and springs: a combinatorial approach*](https://arxiv.org/abs/2506.18693v2), arXiv:2506.18693v2；Phys. Rev. E 113, 014143 (2026)。

论文的 Eq. (2)--(3) 对 free/pinned 随机质量--弹簧链给出谱行列式的精确有限多项式展开及 coefficient multiple-sum 表示；这与本地 transfer recurrence/monodromy polynomial 路线兼容，可作为有限代数的推导指南。

但 Eq. (4) 的 complex Lyapunov exponent 公式依赖对 Eq. (3) coefficients 的 symmetrization。作者明确写明该式不是 exact；后续的 low-frequency density 与 localization exponents 是由这条近似公式及 analytic continuation 得到。因此不能把其 `rho(lambda) ~ lambda^(-1/2)` 或 `gamma(lambda) ~ lambda` 直接作为 frozen periodic chain 的 Lean theorem 输入。它也不含 nonlinear marked eigenvector-overlap measure、collision connectivity 或 kinetic-time remainder，故不解除 B1--B4。
