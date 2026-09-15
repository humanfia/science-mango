# Physical progression and bounded order

This implements the second half of source §5. Given the repaired anchored supports with cardinality w, total integer gcd one, the first-block cutoff and unchanged second-block bound, use the ordinary gcd period to prove exact realization at every sufficiently large T+jE and at an order below birthBound.

The input is precisely the output intended from stage22, with F equal to the tuple signature. This stage does not assume a physical realizing order. The realizes predicate explicitly requires positive order, weight in both blocks, anchors, exponent ranges, connectivity, and exact complete signature. No squarefree premise, distance, inherited intersection or anchored sorting requirement is added.

Imports are the immutable audited90 checkpoint. Full arbitrary-pattern construction will combine this stage with stage22; arithmetic counts remain separate.
