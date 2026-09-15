# M6 formalization status

**Complete original M6 accepted.** The frozen theorem is `M6.Final.original_m6 : M6.Final.OriginalM6`; see [ROOT_ACCEPTANCE.json](ROOT_ACCEPTANCE.json) and [the final compiled experiment](final/seal/experiment/result.json).

291 named targets in the completed batches below passed assembly and unchanged-environment checks. Counts are not completion percentages.

| Completed batch | Accepted targets |
|---|---|
|cyclic|6|
|kernel_fibers|6|
|transfer|7|
|physical|12|
|coordinates|11|
|boundary_fibers|7|
|character|8|
|pinned_recovery|14|
|transfer/resources|6|
|flatten|9|
|spaces|9|
|character/pinned|4|
|character/fibers|5|
|css_distance|7|
|transfer/trace|6|
|transfer/coefficients|8|
|transfer/scatter|7|
|transfer/actual_resources|4|
|transfer/factor_bounds|4|
|normalize|4|
|fixed_span|7|
|transfer/partial_resources|6|
|transfer/indexed_array|1|
|actual_transfer|6|
|enumerator|3|
|actual_counts|10|
|actual_counts/cardinality|9|
|actual_css|7|
|actual_transfer/trace_counts|2|
|actual_result|7|
|zero_span|8|
|euclid|21|
|recipe_isometries|17|
|transfer/weight_resources|2|
|transfer/query_resources|6|
|transfer/postprocessing|5|
|transfer/post_safety|2|
|transfer/solve_resources/query_count|1|
|transfer/solve_resources|2|
|euclid_storage|13|
|transfer/recovery_layout|2|
|transfer/solve_storage|1|
|final/core|6|
|final/seal|3|

The complete theorem connects actual sparse Q enumeration, exact coefficient division, true CSS distance and minimum witnesses, k=2f, concrete work and complete storage bounds, fixed-span improvement, allowed recipe isometries and the zero-span cases. The combined theorem and a fresh independent frozen-target/imported-axiom audit both passed, using only propext, Classical.choice and Quot.sound. Complexity is the original indexed-array bit model.

Model: gpt-6-astra / medium; at most16 proof workers per DAG, five attempts, Mathlib and Physlib retrieval, frozen exact targets and standard-axiom checks. Interrupted runs and exact tactic/specification repairs are archived explicitly.
