# Current M5 formalization progress

Stages 1–22 and 24–25 are complete: 123 named component lemmas accepted by Lean, with combined compilation per batch. A union of 90 components (stages 1–15, 17, 18) also passed single-project compilation and independent exact-type/axiom audit (integrated90).

New accepted components include exact subset and repeated-tuple character counts, finite Boolean inclusion-exclusion, distinct irreducible factor products with the residual cyclic cap, and the gcd/cutoff ingredients for the actual support repair. Original failure histories and successful repair provenance are retained.

Active:
- Stage16 complete: multiplicity-sensitive exact signature criterion and finite residual-factor reduction.
- Stage20 complete: exact arithmetic n(P,W,k,z), including denominator cancellation and nonnegativity.
- Stage21 complete: quotient congruence, packing and replacement preserve complete signature.
- Stage22 complete: actual bounded connected support construction from feasible anchored residue tuples.
- Stage23: exact polynomial signature indicator experiment running with verified stage16 imports.
- Stage24 complete: exact arithmetic repeated-residue count R and nonnegativity.
- Stage25 complete: literal-support progression and actual physical order below birthBound.
- Stage26: anchored single-block arithmetic count experiment running.
- Stage27: exact finite-order arithmetic C and semantic count DAG in preparation.
- Stage28: combining feasible residue patterns with bounded physical realization/progression; accepted dependency import in progress.
- Stage29: anchored/divisor-restricted R count is in preflight.

Settings: gpt-6-astra / medium, proof concurrency ceiling 16, five attempts per node. Successful identical retrievals are cached with provenance within a run; retrieval requests are serialized to reduce rate-limit failures.

Full M5 is not yet formally verified. The complete polynomial inclusion-exclusion and counting/reconstruction chain, final bounded construction and birth/later-order integration, and executable arithmetic refinements remain. The component count is not a percentage of the full theorem; no stronger mathematical goal has been substituted.
