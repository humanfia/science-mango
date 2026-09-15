# Stage42 accepted: exact conditional arithmetic residue count

All six frozen targets and their combined assembly passed. The selected-prefix lists preserve repetition and cancellation, and overfull prefixes are explicitly guarded to zero. Imported original types and permitted axioms were audited before launch.

| Target | Attempts | Result |
|---|---:|---|
| M5.ConditionalResidueCount.prefix_gcd_divisibility | 1 | accepted |
| M5.ConditionalResidueCount.pair_indicator_exact | 1 | accepted |
| M5.ConditionalResidueCount.selected_R_pair_count | 1 | accepted |
| M5.ConditionalResidueCount.arithmetic_indicator_expansion | 1 | accepted |
| M5.ConditionalResidueCount.exact_conditionalA | 2 | accepted |
| M5.ConditionalResidueCount.period_conditionalA_exact | 1 | accepted |

The divisor/factor arithmetic conditionalAAt equals the exact guarded completion-pair cardinality. At the signature period, conditionalA is nonnegative and positive exactly when the prefixes fit and a feasible completion exists. Remaining lengths and selected polynomials can differ between the two blocks. No distinctness, weight upper bound, squarefree or nonzero-block assumption is added. Literal squarefree-divisor reindexing is not an acceptance gate. The concrete recovery connection is subsequent work.

See [result](experiment/result.json), [combined source](experiment/AcceptedExperiment.lean), [preflight/import audit](PREFLIGHT.json), and [manifest](experiment/MANIFEST.json).
