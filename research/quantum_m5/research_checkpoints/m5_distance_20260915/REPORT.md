# M5 构造的精确逻辑距离（2026-09-15）

已完成 M5 已审阅验算记录中的全部 11 个具体构造，以及每个构造在固定 supports 下沿指定序列后移两步（N+E、N+2E）的距离计算。共 33 个实例：30 个 k>0 实例取得精确距离，3 个 k=0 实例没有非平凡逻辑算符，逻辑距离记为不适用。

这里 [[n,k,d]] 的 n=2N 是物理量子比特数，k=2 deg(F) 是逻辑量子比特数；d 是非平凡逻辑 Pauli 算符的最小重量。

| 原记录索引 | T | w | F（多项式位编码） | 原构造 [[n,k,d]] | 第一次 lift [[n,k,d]] | 第二次 lift [[n,k,d]] |
|---|---|---|---|---|---|---|
| 0 | 1 | 2 | 3 | [[12,2,2]] | [[14,2,3]] | [[16,2,4]] |
| 1 | 1 | 3 | 1 | [[20,0,不适用]] | [[26,0,不适用]] | [[32,0,不适用]] |
| 2 | 1 | 4 | 3 | [[26,2,4]] | [[34,2,4]] | [[42,2,4]] |
| 3 | 2 | 4 | 5 | [[68,4,5]] | [[76,4,5]] | [[84,4,5]] |
| 4 | 3 | 3 | 7 | [[90,4,8]] | [[96,4,8]] | [[102,4,8]] |
| 5 | 3 | 4 | 9 | [[126,6,6]] | [[138,6,6]] | [[150,6,6]] |
| 6 | 4 | 4 | 15 | [[192,6,7]] | [[200,6,7]] | [[208,6,7]] |
| 7 | 4 | 4 | 17 | [[200,8,6]] | [[216,8,6]] | [[232,8,6]] |
| 8 | 5 | 4 | 33 | [[290,10,6]] | [[310,10,6]] | [[330,10,6]] |
| 9 | 6 | 4 | 27 | [[384,8,9]] | [[396,8,9]] | [[408,8,9]] |
| 10 | 6 | 4 | 65 | [[396,12,6]] | [[420,12,6]] | [[444,12,6]] |

## 对应的具体 supports

| 索引 | N | A | B | E |
|---|---|---|---|---|
| 0 | 6 | [0, 3] | [0, 1] | 1 |
| 1 | 10 | [0, 2, 4] | [0, 1, 2] | 3 |
| 2 | 13 | [0, 2, 3, 5] | [0, 1, 2, 3] | 4 |
| 3 | 34 | [0, 4, 6, 10] | [0, 1, 2, 3] | 4 |
| 4 | 45 | [0, 2, 10] | [0, 1, 2] | 3 |
| 5 | 63 | [0, 6, 9, 15] | [0, 1, 3, 4] | 6 |
| 6 | 96 | [0, 8, 12, 20] | [0, 1, 2, 3] | 4 |
| 7 | 100 | [0, 8, 12, 20] | [0, 1, 4, 5] | 8 |
| 8 | 145 | [0, 10, 15, 25] | [0, 1, 5, 6] | 10 |
| 9 | 192 | [0, 12, 18, 30] | [0, 1, 3, 4] | 6 |
| 10 | 198 | [0, 12, 18, 30] | [0, 1, 6, 7] | 12 |

## 精确性的证据

使用二元 CSS 矩阵 H_X=[A|B]、H_Z=[Bᵀ|Aᵀ]。求解 X 型距离时，要求 H_Z v=0 且 v 不属于 row(H_X)。由 ker(H_X)/row(H_Z) 的一组基构造非零逻辑 syndrome 的 SAT 约束。

下界查询是“是否存在重量 ≤ d−1 的非平凡逻辑算符”，不预设目标下界。循环平移把所有候选覆盖为两个情形：左块非空并平移到左第 0 位为 1；或左块全空并平移到右第 0 位为 1。两者均 UNSAT 才得到下界。物理坐标反演加两块交换将 H_X 映到 H_Z，保持重量，所以 d_X=d_Z，所得就是量子距离。

30 个实例各保存一个重量 d 的逻辑算符见证，以及两个重量 d−1 无解的 CNF/DRAT 证书，共 60 个证书。独立 drat-trim 检查器已逐一验证；复核脚本重新生成 CNF 与存档逐子句比较，并用 GF(2) 行消元验证见证确实不属于稳定子空间。还重新核验了连通性、完整多项式 gcd signature、矩阵秩和 k。

测试额外遍历 N=2,…,5 的 54 个小码，与全部物理二进制算符的穷举距离逐一对照；另有非法 supports 和超时不能冒充下界的测试。

例：[[90,4,8]] 的 X 逻辑算符支持为 [0,37,38,39,41,42,44,82]；[[384,8,9]] 的支持为 [0,154,155,156,190,191,346,352,358]。索引从 0 开始，前 N 位为左块，后 N 位为右块。

## 固定 supports 的无限 lift：一个距离上界

除上述有限实例的精确值外，还可直接得到一个适用于固定 supports 的上界。令 a,b 为普通多项式，G=gcd(a,b)，a=G a₀，b=G b₀。在任意保持非平凡 signature F=gcd(G,xᴺ+1)≠1、且原 supports 均小于 N 的 lift 上，

**d(N) ≤ wt(a₀)+wt(b₀)。**

证明：向量 (a₀,b₀) 满足 b a₀+a b₀=0，因此与 Z 校验对易。如果它是 X 稳定子，就存在 h 使 (a₀,b₀)=h(a,b) mod (xᴺ+1)。由 gcd(a₀,b₀)=1 的 Bézout 恒等式，得到 1=hG mod (xᴺ+1)。这与 G 和 xᴺ+1 有非平凡公因子 F 矛盾。因此该向量是非平凡逻辑算符，给出上述上界。复核脚本也检查了每个实例的此类见证。

这个上界对同一对固定 supports 不随 N 增长。因此 M5 的固定 supports 无限 lift 本身不能保证距离无界增长。上界不必等于精确距离，例如 N=6 时该上界为 4，而精确距离为 2。

## 范围

完成的是现有 11 个验算构造及其前两次 lift 的精确距离，以及上述固定 supports 的一般上界。没有声称得到所有允许 signature、所有可选 supports、所有码长的统一精确距离公式。此次结果作为距离补充保存，不修改已审阅的 M5 证明，也不增加 M5 的验收门槛。

## 文件与复现

- 原始输入：`../period_residue_arithmetic_law_reviewed/verification/test-results.json`；SHA-256 记录在结果中。
- 原构造：`results.json`、`verification.json`、`proofs/`。
- lift：`lift_inputs.json`、`lifts/results.json`、`lifts/verification.json`、`lifts/proofs/`。
- 计算：`../../scripts/distance_m5.py`；证据复核：`../../scripts/verify_distance_m5.py`。
- 依赖固定在 `requirements.txt`；Python 版本见 `environment.json`。

从研究仓库根目录执行（DRAT_TRIM 指向 drat-trim 可执行文件）：

```bash
.venv-m5-distance/bin/python -m unittest tests.test_distance_m5
.venv-m5-distance/bin/python scripts/distance_m5.py
.venv-m5-distance/bin/python scripts/distance_m5.py --input research_checkpoints/m5_distance_20260915/lift_inputs.json --output research_checkpoints/m5_distance_20260915/lifts/results.json
.venv-m5-distance/bin/python scripts/verify_distance_m5.py --drat-trim "$DRAT_TRIM"
.venv-m5-distance/bin/python scripts/verify_distance_m5.py --results research_checkpoints/m5_distance_20260915/lifts/results.json --drat-trim "$DRAT_TRIM"
```
