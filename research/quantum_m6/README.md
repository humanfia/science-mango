# M6 证明、算法与验收结果

**原始 M6 已按“有证明的精确距离计算简化”路线完成验收。**
本目录发布完整自然语言证明、独立双审阅记录、冻结算法及验证证据。

## 统一入口

- [最终完整证明与原始验收条款论证](research_checkpoints/m6_original_gate_closed_20260915/PROOF.md)
- [最终验收记录](research_checkpoints/m6_original_gate_closed_20260915/integration-decision.json)
- [最终独立审阅 A](research_checkpoints/m6_original_gate_closed_20260915/call-008-review.json)、[审阅 B](research_checkpoints/m6_original_gate_closed_20260915/call-009-review.json)
- [冻结实现重跑结果](research_checkpoints/m6_original_gate_closed_20260915/verification-replay.json)
- [可执行算法与验证](research_checkpoints/m6_all_order_transfer_20260915/verify_transfer.py)
- [M1–M8 路线图及当前状态说明](ROADMAP.md)
- [新增 M8：任意跨度的精确距离计算复杂性](ROADMAP.md#121-m8-arbitrary-span-exact-distance-complexity)（待研究）
- [M5 证明与距离材料](../quantum_m5/README.md)

## 证明了什么

对声明的连通、等正权重、二元循环双块 CSS 码族，算法覆盖每个合法
码长 N>R；R 是选定 supports 表示的最大指数。保留完整 gcd 的重复
因子，含偶数码长。非平凡逻辑空间存在时，精确计算距离并构造最小
逻辑算符；否则明确返回没有逻辑距离。

在证明声明的数组位运算模型下：

| 任务 | 界 |
|---|---|
| 精确距离 | O(N³4^R) 位运算 |
| 最小逻辑见证 | O(N⁴4^R) 位运算 |
| 工作存储 | O(N²2^R) 位 |

固定 R 时，关于 N 为多项式，优于逐一枚举 4^N 个物理二进制向量。
这是原路线图允许的精确计算简化及有证明范围；不要求同时解决任意
跨度下的高效算法。此处不宣称实际快于现有求解器、M7 完成、量子码
等价分类完成或 Lean 形式化完成。Python 字典实现的时间保证与论文
式数组模型有区别，最终证明明确说明了这一点。

## 证据与复现

最终冻结候选由两位独立 harness 审阅者审阅，均报告 no_gap_found；
这些审阅记录不代替数学证明。实现检查和有限穷举也不是无限定理的
证明前提。冻结实现重跑通过 99 个小码、790 项带坐标限制的计数比较
及 49 个非平凡逻辑见证检查，包含重复因子和错误坐标方向的负控。

从本目录执行，仅需 Python 标准库：

```bash
python3 -B research_checkpoints/m6_all_order_transfer_20260915/verify_transfer.py
python3 -B research_checkpoints/m6_fixed_support_stabilization_20260915/verify_optimizer.py
```

[来源哈希清单](SOURCE_MANIFEST.json) 保留导入文件的精确字节哈希。
各阶段的依赖文件与依赖哈希随证明归档，可离线检查。

## 阶段记录

1. [固定 supports 的最终稳定律](research_checkpoints/m6_fixed_support_stabilization_20260915/README.md)
2. [覆盖所有合法码长的转移矩阵证明](research_checkpoints/m6_all_order_transfer_20260915/PROOF.md)
3. [原始 M6 验收论证与最终整合](research_checkpoints/m6_original_gate_closed_20260915/README.md)

冻结历史文件中的“尚待审阅”“尚未推送”等句子反映各文件写作时的
状态；当前发布及验收状态以本入口和最终验收记录为准。原始 harness
的 research_goal_proved=false 是其保守交回主控的记录，未被改写；
最终范围明确的验收决策另存于 integration-decision.json。
