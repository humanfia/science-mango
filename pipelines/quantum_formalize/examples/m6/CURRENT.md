# M6 formalization status

In progress; complete M6 has not yet been formally accepted.

266 named targets in the completed batches below passed assembly and unchanged-environment checks. Counts are not completion percentages.

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

The actual sparse Q enumerator, minimum witness recovery, actual CSS distance correspondence, k=2f, fixed-span improvement, recipe isometries and zero-span cases are accepted as components. Final original-scope core composition is running. Remaining resource work is the actual Euclidean slot-storage closure and its final solve-storage specialization. No complete-M6 root acceptance is asserted yet.

Model: gpt-6-astra / medium; at most16 proof workers per DAG, five attempts, Mathlib and Physlib retrieval, frozen exact targets and standard-axiom checks. Interrupted runs and exact tactic/specification repairs are archived explicitly.
