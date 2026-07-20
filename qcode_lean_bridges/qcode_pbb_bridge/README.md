# qcode_pbb_bridge — PBB 非CSS 码 · 块内对易性 → Lean 4

用 `bridge_pbb.py` 把 qcode-discovery 的 **perturbed bivariate-bicycle (PBB) 非CSS**
量子码目录(`campaign7_publication_merged.jsonl`)转成 Lean 4 形式化目标,claim 为
**块 1 内 X/Z 稳定子对易性**:

    M := A·Cᵀ + B·Dᵀ  在反极对称下不变   M = Mᵀ   (over 𝔽₂)

## 与 CSS 的区别(为什么这是"更硬"的 claim)

CSS 正交性 `A·B + B·A = 0` 对**所有**码恒成立(交换环+特征 2,证明与码无关)。
PBB 对易性**不是恒等式** —— 它是每个码的**真算术事实**,只对合法构造的码成立。
qcode-discovery 用 `evaluation/pbb_code.check_commutativity` 强制此条件:

    M = (A @ Cᵀ + B @ Dᵀ) % 2   必须等于   Mᵀ

其中 `Cᵀ` 是反极(antipode):单项式 `x^a·y^b` 的转置为 `x^(-a)·y^(-b)`,故
A 的 `x^a·y^b` 乘 Cᵀ 的 `x^(-c)·y^(-d)` 贡献 `x^(a-c)·y^(b-d)`,系数在 𝔽₂ 里 XOR 抵消。

## 数学建模(Lean)

多项式取其 𝔽₂ support,建模为 `List (ZMod ℓ × ZMod m)`。
- `mulT P Q`:`P·Qᵀ` 的 support,把所有单项式 `p - q`(对 Q 取反极)XOR 折叠。
- `M = A·Cᵀ + B·Dᵀ`(𝔽₂ 加法 = support 的 XOR)。
- claim `∀ g ∈ M, (-g) ∈ M`(即 `M = Mᵀ`),用 `decide` 在 kernel 里判定,
  外套 `set_option maxRecDepth 100000`(大环 `ZMod 30` 递归较深)。

**为何用 `decide` 而非 `native_decide`**:`Finset.toList` 是 noncomputable,
会毙掉 `native_decide`;改用 `List` 模型后 `decide` 可直接 kernel 归约,
axiom profile 干净(仅 `propext / Classical.choice / Quot.sound`,**无 sorryAx、
无 ofReduceBool**),soundness 强于 `native_decide`。

## 生成

    python3 ../bridge_pbb.py \
        --catalog ../qcode-discovery/results/campaign7_publication_merged.jsonl \
        --out     . \
        --lib-name PBB \
        [--sorry]        # 发 `by sorry` 桩,交给 archon prover 端到端补证

产物:
- `PBB/<module>.lean` — 每码一个自包含、**完整证明、0-sorry** 文件,
  套 `namespace <module>` 避免 A/B/C/D/M 命名冲突。module 名取 `code_id`。
- `PBB.lean` — 根模块,import 全部码文件。
- `objectives.jsonl` — 每行一个 archon objective,含自然语言 claim +
  `A/B/C/D_terms`/`ell`/`m`/`n`/`k`/`d`/`code_id` + `target_theorem`。

## 验证状态(2026-07-20)

- 数据甄别:`benchmark_noncss.json` 的 ptb_66 记录 **0/65 通过** qldpc
  `build_pbb_code` 的对易性检查(那是**预筛候选**,非合法码);
  改用 **`campaign7_publication_merged.jsonl`**,`build_pbb_code` **60/60 通过**,
  且全部 **368/368** 在 `M = A·Cᵀ + B·Dᵀ`、项 `(a-c)` 约定下反极对称。
- 全量生成 **368 个非CSS 码**,7 种 (ℓ,m) 环:(3,6)(6,3)(6,6)(9,6)(12,6)(15,6)(30,6)。
- 每环各抽一代表 `lake env lean` 编译 → **7/7 通过**(含最大 (30,6) n=360)。
- 3 文件多 namespace 共存编译 → **3/3 通过**。
- **非平凡性验证**:构造一个反例码(故意不对易),`decide` **成功证伪**该 claim,
  说明 objective 真在校验内容,而非空真。
- axiom 检查:`#print axioms pbb_commute` = `[propext, Classical.choice, Quot.sound]`,0 sorryAx。

## 接入 archon

同 CSS 桥:生成文件已带完整证明,可直接 `lake build`(0 sorry);要跑
`archon loop`(prover 补证),用 `--sorry` 生成桩,或把 `objectives.jsonl` 喂给
`archon physics-formalize --input-jsonl objectives.jsonl`。

注意:`campaign7` 记录用 `ell`/`m`(不是 CSS 的 `label`)显式给出环阶;module 名
取自 `code_id`(如 `30_6_0260`),个别早期记录 code_id 为 `phase2_N`。
