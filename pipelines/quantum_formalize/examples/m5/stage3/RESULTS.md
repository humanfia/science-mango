# Stage 3 results — exact mathematical period law

All six frozen targets passed Lean acceptance and assembled compilation. Together with stages 1 and 2, 23 individual lemmas have been accepted.

For every monic binary polynomial F with constant coefficient one, the period is positive and satisfies F | (X^N+1) iff t(F) | N for every natural N. Also t(1)=1, and inclusion F|G implies t(F)|t(G) within the signature domain. The quotient is the full AdjoinRoot ring: no irreducibility or squarefreeness assumption was used, and the F=1 quotient is allowed to be trivial.

| Node | Attempts |
|---|---:|
| cyclic_dvd_iff_root_pow | 2 |
| quotient_finite | 1 |
| root_is_unit | 1 |
| period_law | 1 |
| period_dvd_of_dvd | 1 |
| period_one | 1 |

The definition uses noncomputable `orderOf`; this completes the mathematical period-law component, not an executable period-search refinement. The original arithmetic-workflow obligation is retained separately. The other global M5 obligations are not automatically discharged by this component.

[Assembled Lean proof](experiment/AcceptedExperiment.lean), [acceptance receipt](experiment/result.json), [status DAG](experiment/GRAPH.md). Archive includes exact targets, dependency proofs, retrieval history, model drafts, compiler output and hashes.
