# Stage25 results

All three exact targets and the combined assembly passed: the ordinary gcd period is positive and bounded, the same literal supports realize the full signature along all sufficiently large T+jE, and an actual positive physical order exists strictly below birthBound. Physical realization includes both cardinalities, zero anchors, exponent ranges, connectivity and complete signature.

The initial automatic period-control proof failed five attempts. Its explicit proof uses the already accepted coefficient/gcd/period lemmas, with no statement changes. The repair replay and the two downstream proofs each passed their first attempts. [REPAIR_REPLAY.json](REPAIR_REPLAY.json) preserves the split; [initial evidence](experiments/initial_tactic_failure/result.json) remains intact.

[Accepted assembly](experiment/AcceptedExperiment.lean), [receipt](experiment/result.json), [DAG](experiment/GRAPH.md).

This stage starts from repaired finite supports with the stated bounds, not an existing realizing order. Stage28 connects it to stage22's construction from feasible residue tuples. Full M5 remains pending arithmetic count/recovery and final integration.
