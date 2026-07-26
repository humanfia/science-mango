# qcode_k_bridge — BB 码逻辑维数 k → Lean 4

用 `bridge_k.py` 把 qcode-discovery 的 **bivariate-bicycle (BB) CSS** 码目录
(`results/ilp_catalog.json`)转成 Lean 4 形式化目标,claim 为**逻辑维数**:

    k = n − rank₂(H_X) − rank₂(H_Z)      n = 2·ℓ·m

## 为什么这是三个 claim 里"最硬"的

| 桥 | claim | 性质 |
|----|-------|------|
| CSS 正交 | `A·B + B·A = 0` | 对所有码恒成立(交换环 + 特征 2),证明与码无关 |
| PBB 对易 | `M = A·Cᵀ + B·Dᵀ` 反极对称 | 每码的真算术事实,但仍是单个代数等式 |
| **逻辑维数 k** | `n − rank₂(H_X) − rank₂(H_Z) = k` | 需真正**算两个奇偶校验矩阵的秩**——一次线性代数计算,值区分不同码 |

前两者是"某个代数式等于 0 / 对称";k 要在 kernel 里跑一遍 **𝔽₂ 高斯消元**求秩。
算错任何一个循环矩阵项都会得到错的 k,`decide` 直接证伪(见下方非平凡性验证)。

## 循环矩阵约定(已对 qldpc 校准)

    G = [(a,b) for a in range(ℓ) for b in range(m)]        # 索引顺序
    circ_P[i][j] = 1  ⟺  (G[j] − G[i]) mod (ℓ,m) ∈ supp(P)
    H_X = [circ A | circ B]        (ℓm × 2ℓm 块循环)
    H_Z = [circ Bᵀ | circ Aᵀ]

`kmask.py` 用此约定重算全目录 **156/156 码的 k 全部与标注吻合**。

## Lean 建模

每行奇偶校验打包成一个 `Nat` 位掩码(LSB = 第 0 列),整块矩阵是 `List Nat`。
- `reduceStep`:把向量 `v` 对"每元素占据唯一最高位"的 𝔽₂ 基做完全归约(`fuel = 2n` 封顶)。
- `rankF2 rows`:对每行归约,非零则加入基,基的长度即秩。
- claim `n − rankF2 Hx − rankF2 Hz = k`,`decide` 在 kernel 归约。

**为何用 `decide` 而非 `native_decide`**:`decide` 走 kernel,axiom profile 干净
(仅 `propext`,**无 ofReduceBool、无 sorryAx**),soundness 强于 `native_decide`。
大码(n=288/360)的秩计算算力较大,故套两个 `set_option`:

    set_option maxHeartbeats 10000000 in     -- 默认 200000 不够
    set_option maxRecDepth   1000000  in

> **踩坑记录**:n=288/360 起初报 `(deterministic) timeout at whnf, maximum number
> of heartbeats (200000) has been reached`——**不是文件数、不是内存**(全程 ~7–8.5 GB,
> 机器 440 GB 空闲),而是 kernel `decide` 跑大矩阵高斯消元超出默认心跳预算。
> 加 `maxHeartbeats` 即通。

## 生成

    python3 ../bridge_k.py \
        --catalog ../qcode-discovery/results/ilp_catalog.json \
        --out     . \
        --lib-name KDim \
        [--limit N] [--sorry]

产物:
- `KDim/<module>.lean` — 每码一个自包含、**完整证明、0-sorry** 文件,套 `namespace <module>`。
- `KDim.lean` — 根模块,import 全部码文件。
- `objectives.jsonl` — 每行一个 archon objective,含自然语言 claim +
  `A_terms/B_terms/ell/m/n/k/label` + `target_theorem`(`<module>.k_logical`)。

## 验证状态(2026-07-20)

- 数据:`ilp_catalog.json` 共 **156 码**,4 组:n=144(32)、n=288(59)、n=360(63)、
  bravyi_baselines(2:[[72,12,6]]、[[144,12,12]])。
- k 甄别:`kmask.py`(numpy-free 纯 Python 𝔽₂ 高斯消元)重算全部 **156/156** k 与标注吻合。
- 规模阶梯逐一 `lake env lean` 编译,`decide` 全部通过:

  | n | 时间 | 峰值内存 | 结果 |
  |---|------|----------|------|
  | 72  | 7.7 s   | 6.6 GB | ✅ |
  | 144 | 9.3 s   | 6.9 GB | ✅ |
  | 288 | 加心跳后 | 7.0 GB | ✅ |
  | 360(最大)| 8m38s | 8.5 GB | ✅ |

- **非平凡性验证**:把 [[72,12,6]] 的 claim 从 `= 12` 改成 `= 13`,`decide` **成功证伪**
  (`Tactic 'decide' proved that the proposition ... is false`),说明 objective 真在校验
  秩的算术,而非空真。
- axiom 检查:`#print axioms k_logical` = `[propext]`,0 sorryAx、0 ofReduceBool——
  比 CSS/PBB 桥(`propext/Classical.choice/Quot.sound`)还干净。

## 接入 archon

生成文件已带完整证明,可直接 `lake build`(0 sorry);要跑 `archon loop`(prover 补证),
用 `--sorry` 生成桩,或把 `objectives.jsonl` 喂给
`archon physics-formalize --input-jsonl objectives.jsonl`。

注意:大码(n≥288)`decide` 单文件编译可达数分钟(n=360 约 8.6 分钟),批量 `lake build`
需相应放宽超时。
