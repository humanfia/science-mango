# Stage31 accepted: original arithmetic residue count A

All six frozen targets and their combined assembly passed. Exact imported proof types and permitted axioms were audited before launch; all mathematical target statements were preserved.

| Target | Attempts | Result |
|---|---:|---|
| M5.ResidueCount.pair_indicator_exact | 1 | accepted |
| M5.ResidueCount.two_block_R_count | 1 | accepted |
| M5.ResidueCount.arithmetic_indicator_expansion | 4 | accepted |
| M5.ResidueCount.exact_rawA | 3 | accepted |
| M5.ResidueCount.rawA_nonnegative_and_positive | 1 | accepted |
| M5.ResidueCount.period_A_exact | 1 | accepted |

The original divisor/factor arithmetic rawA equals the cardinality of feasible anchored tail pairs. At T=signaturePeriod F, A is nonnegative and positive exactly when such tails exist. The statement retains empty tails, repeated residues, polynomial cancellation and raw-coordinate integer gcd. No distinctness, weight upper bound, squarefree or nonzero-block assumption was added. Literal squarefree-divisor reindexing is not an acceptance gate. Full M5 assembly remains separate.

See [result](experiment/result.json), [combined source](experiment/AcceptedExperiment.lean), [preflight/import audit](PREFLIGHT.json), and [manifest](experiment/MANIFEST.json).
