# M7 证明与形式化

原始 M7 的完整自然语言证明与 Lean 总定理 `M7.Final.original_m7` 均已完成验收。

- [完整 Lean 验收记录](../../pipelines/quantum_formalize/examples/m7/final/ROOT_ACCEPTANCE.json)
- [总定理与八个章节的编译证明](../../pipelines/quantum_formalize/examples/m7/final/experiment/AcceptedExperiment.lean)

- [冻结自然语言证明](research_checkpoints/m7_compact_selector_final_20260915/PROOF.md)
- [自然语言验收与独立审阅](research_checkpoints/m7_compact_selector_final_20260915/integration-decision.json)
- [Lean 形式化入口](../../pipelines/quantum_formalize/examples/m7/README.md)
- [形式化依赖图](../../pipelines/quantum_formalize/examples/m7/GRAPH.md)

原目标是通过紧凑算术生成与精确距离标签，返回请求参数下全部经过认证的最优类及并列实现；保留完整重因子、NoLogical 和空答案。M8 任意跨度高效性属于单独目标。冻结历史归档中的未发布或待形式化说明保留原样，当前状态以本入口和 Lean 验收记录为准。
