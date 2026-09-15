# 原始 M5 完成记录：精确算术 birth/lift 工作流

更新：2026-09-14 16:13 UTC。

**原始 M5 的 sector 生成／例外判定目标已由一份统一算术证明完成，并通过两份独立审查。** 完成范围是交接文档原有的正支撑重量、二元循环双块配方族：每个允许的完整 signature 在每个阶数都能生成，或者被证明不能出现。没有把 inherited 交集、anchored 排序、算法效率或距离结论加入门槛。

## 证明及记录

- 可读完整证明：[PROOF.md](../research_checkpoints/period_residue_arithmetic_law_reviewed/PROOF.md)。
- 冻结、带依赖哈希的候选稿：[proof-8b2c4…](proof-8b2c4aa48c1c555c1d9b058fc632426c415d5023a0859be252e0603ba2517227.md)。
- 两份审查：[review-result.json](../research_checkpoints/period_residue_arithmetic_law_reviewed/review-result.json)。二者均核查同一完整候选稿，结论为 `no_gap_found`，且明确认可原始 M5 范围。
- 候选稿哈希：`5f23d6908129f246885865e3ccb27f7138ebb3dcd5246010998a84d50b49f770`。
- 审查运行：`run-n0nf8_pg`，模型均为 `gpt-6-astra / medium`。

## 实际证明了什么

给定正重量 w 和完整二元多项式 signature F，保留所有重复因子：

1. 显式字符和与 Möbius 公式 A_w(F) 精确判定 F 是否能在任何连通循环阶数出现。
2. 若能出现，周期残余模式恢复、支撑打包及 CRT 修复构造真实配方。对 w≥2，首次出现满足统一界
   `b(F,w) ≤ w T(T+2) + 2^(wT)`，其中 `T=t(F)`。
3. 对任意指定阶数 N，显式整数 C_(N,w)(F) 精确计数连通、完整 signature 恰为 F 的锚定有序支撑对。正数通过条件计数恢复配方；零严格证明该阶数不可能。
4. 在有界区间内计算首次正计数即可确定精确 birth；相同的 C 公式与恢复算法覆盖其后每个阶数。不是把某条充分条件失败当作不可能。
5. 非常数、可实现的重量三 F 的首次出现进一步简化为 `t(F)`。重量三 F=1 首次出现为 4，且所有 N≥4 均出现。

这些是对所有参数的符号证明与终止算法。算法枚举有限环的加性字符和因子，不扫描原始支撑对；可能非常昂贵，不主张速度优势。完整配方群保持为独立平移、公共单位乘子及块交换。

## 检验与验收说明

统一结论来自字符正交、两层容斥、CRT 连通性修复和有限环周期证明；有限实验及审查票数不是证明前提。小规模排错另行通过：242 个精确计数案例与 4707 对测试支撑一致，41 个物理配方恢复案例成功，39 个周期残余计数案例一致，11 个残余恢复／打包／周期构造案例成功。脚本与结果保存在证明归档的 `verification/`。

Harness 原始状态 `reviewed_candidate_pending_manual_integration` 与 `research_goal_proved=false` 是该工具保留给外层采纳判断的设计；它不自动把模型审查变成数学证明。这一状态原样保留。外层已检查完整推导、相同稿件的两份审查和原始目标对应关系，在单独的 [integration-decision.json](../research_checkpoints/period_residue_arithmetic_law_reviewed/integration-decision.json) 中采纳此证明，未改写工具结果，也未新增第三轮或更强目标。

原始交接文档及旧覆盖稿中 M5“开放”的文字描述的是当时状态；它们作为冻结依赖保留。当前状态以本记录和完整证明为准。M6 距离、M7 全部最优选择器以及其他可选研究问题不因此完成，也不阻止本次 M5 完成。

原主运行 `run-x3n033k7` 的综合稿已先完成两份审查并归档，然后于下一 dispatcher 边界停止。没有丢弃已完成证明，没有把取消的探索任务记为数学失败。本次证明包包含完整证明、冻结依赖、两份独立审查及可复现的小规模排错脚本。
