# qcode_bridge — BB 码 CSS 正交性 → Lean 4

用 `bridge_css.py` 把 qcode-discovery 的 bivariate-bicycle (BB) 量子码目录
(`ilp_catalog.json`)转成 Lean 4 形式化目标,claim 为 **CSS 正交性**:

    H_X · H_Zᵀ = A·B + B·A = 0   (over 𝔽₂)

## 数学建模

BB 码定义在环面 `Z_ℓ × Z_m` 上,校验多项式 A、B 属于群代数
`GA = AddMonoidAlgebra (ZMod 2) (ZMod ℓ × ZMod m)`。单项式 `x^a·y^b` 编码为
基元 `single (a, b) 1`。

因为 GA 是 **交换环 + 特征 2**:
`A·B + B·A = A·B + A·B` (mul_comm) `= 0` (CharTwo.add_self_eq_zero)。
证明对所有码相同,只有 A、B 的定义不同。特征 2 实例由系数环 `ZMod 2`
经(单射)代数映射提升:`charP_of_injective_ringHom`。

## 生成

    python3 ../bridge_css.py \
        --catalog ../qcode-discovery/results/ilp_catalog.json \
        --out     . \
        --lib-name QCode

产物:
- `QCode/<module>.lean` — 每个码一个自包含、**完整证明、0-sorry** 的文件,
  每个文件套 `namespace <module>` 避免命名冲突。
- `QCode.lean` — 根模块,import 全部码文件。
- `objectives.jsonl` — 每行一个 archon 可摄入的 objective,含自然语言 claim +
  原始多项式数据(`A_terms`/`B_terms`/`ell`/`m`/`k`/`label`)+ `target_theorem`。

## 验证状态（2026-07-20）

- 模板经 Mathlib **v4.32.0** 验证编译通过。
- 全量生成 **156 个码**(n=144/288/360 三组 + 2 个 bravyi baseline)。
- 覆盖 7 种 (ℓ,m) 环:每种各抽一个代表 `lake env lean` 编译 → **7/7 通过**。
- 前 3 个码多文件共存(namespace 隔离)编译 → **3/3 通过**。

## 接入 archon

生成的 Lean 文件已含完整证明,可直接 `lake build` 校验(0 sorry)。若要让
`archon loop` 端到端跑（autoformalize→prover），把 `objectives.jsonl` 喂给
`archon physics-formalize --input-jsonl objectives.jsonl`,或将 `QCode/` 拷入一个
`archon init` 出来的 Lean 项目并把 stage 设为 `prover`（文件已带证明，prover 只需
确认无 sorry）。

注意：命名把 `label` 里 `[[n,k,≤d]]` 的所有数字都提取进模块名，个别 label
（如 `[[360,40,≤20]]` 变体）会得到偏长的模块名，但唯一且可编译。
