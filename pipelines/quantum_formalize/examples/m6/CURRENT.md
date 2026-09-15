# M6 formalization status

In progress; complete M6 has not yet been formally accepted.

151 named targets in the completed batches below passed assembly and unchanged-environment checks. Counts are not completion percentages.

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

Active: actual transfer-to-physical input identities, actual fiber/character normalization, Euclidean preprocessing, and final indexed-array integration. The final root must still connect these to the concrete distance/witness evaluator, account for total resources, preserve recipe isometries and edge cases, and pass original-scope acceptance.

Model: gpt-6-astra / medium; up to 16 proof workers per DAG, five attempts, Mathlib and Physlib retrieval, frozen exact targets and standard-axiom checks.
