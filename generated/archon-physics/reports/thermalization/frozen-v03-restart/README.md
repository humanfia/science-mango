# Frozen v0.3 / R32 形式化研究快照与重启说明

日期：2026-09-07

> 这是可复现的研究进度快照，不是“正向完整热化已经证明”的发布说明。

## 快照位置

- 仓库：`https://github.com/humanfia/science-mango`
- 快照分支：`codex/thermalization-r32-snapshot-20260907`
- Lean 项目：`generated/archon-physics`
- Lean 工具链：`leanprover/lean4:v4.33.0`
- Mathlib：`v4.33.0`
- PhysLean/Physlib：`846bc6814ee141aa945d7385646b6e45385e635e`
- 快照基线：`583e38e8bba79a13679da4a4443b7270935467f1`

最终快照 commit 请在检出分支后用 `git rev-parse HEAD` 读取。恢复时应以该
commit 为准，不要只复制两个顶层 Lean 文件：概率事件、Duhamel、Parseval、
supervolume joint limit 和时钟审计有一条较长的本地依赖闭包。

## 当前准确结论

### 1. 已证明：旧 frozen v0.3 根目标在当前时钟上不成立

旧 frozen root 使用总谐波能量等于 `1` 的 unit-shell 初态，并在物理时间

\[
t=\tau/g^2
\]

读取全部 `N-1` 个正模的 late-window `L1` 距离。

`ArchonPhysics/R32CanonicalSupervolumeUniformNoHitV1.lean` 已针对实际的
canonical random-mass、cubic-leading 一维 FPUT Hamiltonian 证明：对任意
`delta < 1/8` 和任意只给出尺寸下限的 `sizeCutoff`，可以构造一个合法的
supervolume joint limit；在一个概率趋于 `1` 的共同事件上，对每个固定
`T>0` 以及所有 `0 < tau <= T`，完整正模距离始终保持在阈值之上。因此旧
root 所要求的 `g^2 T_eq` 高概率双边界不存在。

关键定理是：

```text
ArchonPhysics.R32CanonicalSupervolumeUniformNoHitV1
  .canonical_supervolume_uniformWindowPersistence

ArchonPhysics.R32CanonicalSupervolumeUniformNoHitV1
  .not_exists_frozen_root_highProbabilityG2Bounds
```

这是实际 Hamiltonian、完整时间窗和同一个高概率事件上的 no-go，不只是固定
终点障碍。它否定的是“unit-total-energy 初态 + lower-only joint-limit 量词
+ `tau/g^2` 时钟”这一组合；它没有证明系统永远不会热化，也没有排除更长
时钟上的热化。

### 2. 已证明：旧 full certificate 接口为空

`ArchonPhysics/R32FrozenFullCertificateNoGoV1.lean` 把上述无条件 no-go 与旧
conditional release theorem 组合，证明：

```text
¬ Nonempty
  (FullThermalizationCertificate
    model actionZero kappa beta hbeta mu delta sizeCutoff)
```

关键定理是：

```text
ArchonPhysics.R32FrozenFullCertificateNoGoV1
  .not_nonempty_fullThermalizationCertificate
```

`mu` 和 `delta` 的合法区间由假设中的 certificate 字段直接给出；空性定理
没有另加 kinetic approximation、persistence 或结论形状的公理。因此问题不再
是“还没有构造旧 certificate”：在原 frozen current-clock 语义下，这种
certificate 已被证明不可能有 inhabitant。

### 3. 已证明：固定能量密度对应的时钟含有体积因子

旧 root 中的 `g` 是 unit-shell Hamiltonian 参数。若把同一模型改按每个物理
site 的固定能量密度解释，public coupling 是

\[
\gamma_{\mathrm{density}}=\frac{g}{\sqrt N},\qquad
\gamma_{\mathrm{density}}^2=\frac{g^2}{N}.
\]

所以对应的 kinetic observation time 为

\[
t=\frac{\tau}{\gamma_{\mathrm{density}}^2}
  =\frac{N\tau}{g^2},
\]

等价地，新的 hitting-time 缩放应研究 `(g^2/N) T_eq`，而不是 `g^2 T_eq`。
相关代数恒等式已在以下模块通过 Lean kernel：

```text
ArchonPhysics/DensityNormalizedFrozenRescalingV4.lean
ArchonPhysics/FrozenUnitShellKineticClockCorrection.lean
ArchonPhysics/FrozenV03RootClockAudit.lean
```

若按 `N-1` 个非平移正模定义密度，相应计数因子是 `N-1`；仓库当前的
density-normalized wrapper 使用每个物理 site 的约定，因此这里采用 `N`。

## 尚未完成的正向目标

当前没有定理从实际 FPUT Hamiltonian 推出系统在 `N tau/g^2` 时钟上达到
equipartition、mixing、ergodicity 或完整热化。

下一阶段应新建一个与旧 frozen root 分离的 repaired-clock specification：

1. 把观测时钟改为 `N tau/g^2`，或把 hitting time 的缩放改为
   `(g^2/N) T_eq`。
2. 重新审计 admissible joint limit；不能默认旧的 lower-only 体积条件在更长
   时间窗上仍足够。
3. 分别证明 early no-hit 和 late hit，而不只证明某个终点的扩散。
4. late endpoint 可继续使用现有的最弱 full-mode scalar port：若归一化模能量
   为 `q_k`、`M=N-1`，证明 `M * sum_k q_k^2 <= 1 + delta^2` 即可推出完整
   正模 `L1 <= delta`。
5. 真正缺少的是 corrected clock 上实际 Hamiltonian 的承重解析估计，包括
   micro-to-kinetic/mean-memory 控制、带符号的全模 aggregate、直接 Q2 和
   Q1/Q1 主项、非线性余项以及与体积一致的概率控制。

不要把旧 `campaign/global-goal.json` 中的 `thermalization.complete` 改成
`verified`。旧 root 的 conditional theorem 与 certificate 空性在逻辑上可以
同时存在，但该 conditional theorem 是不可实例化的真空蕴含，不能当作正向
热化完成。

## 关键源码和审计记录

```text
ArchonPhysics/R32CanonicalSupervolumeUniformNoHitV1.lean
ArchonPhysics/R32FrozenFullCertificateNoGoV1.lean
ArchonPhysics/FrozenUnitShellKineticClockCorrection.lean
ArchonPhysics/FrozenV03RootClockAudit.lean
ArchonPhysicsConsumers/Thermalization/problem_r32_canonical_supervolume_uniform_no_hit.lean
ArchonPhysicsConsumers/Thermalization/problem_r32_frozen_full_certificate_no_go.lean
reports/thermalization/frozen_v03_supervolume_uniform_nohit_clean_build_2026-09-03.md
```

该快照包含上述入口所需的全部新增本地 Lean 依赖，而没有收录原工作树中两千
多个与此结果无关的实验文件。

## 在另一台机器恢复

```bash
git clone https://github.com/humanfia/science-mango.git
cd science-mango
git fetch origin
git switch --track origin/codex/thermalization-r32-snapshot-20260907
git rev-parse HEAD

cd generated/archon-physics
lake update
lake exe cache get
```

如果还没有 Lean，请先安装 Elan；仓库中的 `lean-toolchain` 会选择 Lean
`v4.33.0`。不要复制旧机器上的 `.lake/`、`.olean`、`.venv/` 等本地缓存。

## 建议的复验命令

在 `generated/archon-physics` 中运行：

```bash
lake build ArchonPhysics.FrozenUnitShellKineticClockCorrection
lake build ArchonPhysics.FrozenV03RootClockAudit
lake build ArchonPhysics.R32CanonicalSupervolumeUniformNoHitV1
lake build ArchonPhysics.R32FrozenFullCertificateNoGoV1
lake build ArchonPhysicsConsumers.Thermalization.problem_r32_canonical_supervolume_uniform_no_hit
lake build ArchonPhysicsConsumers.Thermalization.problem_r32_frozen_full_certificate_no_go
```

需要直接查看 axiom 输出时：

```bash
lake env lean ArchonPhysics/FrozenV03RootClockAudit.lean
lake env lean ArchonPhysics/R32CanonicalSupervolumeUniformNoHitV1.lean
lake env lean ArchonPhysics/R32FrozenFullCertificateNoGoV1.lean
```

这些关键入口的预期 axiom 集合只有 Lean/Mathlib 的标准公理：

```text
[propext, Classical.choice, Quot.sound]
```

## 当前 gate 状态

- Lean kernel、定向 library build 和两个 consumer：绿色。
- signature gate：红色，原因是旧终端定理的类型仍含
  `FullThermalizationCertificate`。
- completion gate：红色，根 family 仍是 `unexpanded`，且不存在有效的正向
  completion evidence。这是诚实且预期的状态。
- DAG validator：当前还存在独立的可移植性问题。冻结 v0.2 symbol DAG 本身的
  哈希和证据可验证，但 validator 把 v0.3 source root 与 v0.2 evidence root
  强绑为同一个绝对项目路径。不要通过刷新冻结哈希来掩盖该问题；应为 validator
  增加独立的 verified-base project/root。

详细 no-go clean-build 证据见同仓库的
`reports/thermalization/frozen_v03_supervolume_uniform_nohit_clean_build_2026-09-03.md`。

## 重启后的第一项工作

先保持旧 root 的 no-go/emptiness 结论不变，为 `N tau/g^2` 建立新的目标声明、
observable scaling、joint-limit 条件和 completion gate；然后在 corrected clock 上
选择一个实际 Hamiltonian 的最弱充分 endpoint，并另外补齐 early no-hit。
