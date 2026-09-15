# Current M5 formalization progress

Stages 1–15, 17–19 and 21 are complete: 100 named component lemmas accepted by Lean, with combined compilation per batch. A union of 90 components (stages 1–15, 17, 18) also passed single-project compilation and independent exact-type/axiom audit (integrated90). These counts exclude the four accepted components in the incomplete stage16 batch.

New accepted components include exact subset and repeated-tuple character counts, finite Boolean inclusion-exclusion, distinct irreducible factor products with the residual cyclic cap, and the gcd/cutoff ingredients for the actual support repair. Original failure histories and successful repair provenance are retained.

Active:
- Stage16: repair the strict-divisor extra-factor proof and finish exact polynomial signature exclusion. Four accepted components are preserved, including the repaired strict-divisor lemma.
- Stage20: exact arithmetic n(P,W,k,z) through the binomial/character formula; experiment running.
- Stage21 complete: quotient congruence, packing and replacement preserve complete signature.
- Stage22: bounded connected support construction is running after verified import of its completed dependencies.
- Stage23: exact polynomial signature indicator targets typecheck; proof launch waits for accepted stage16 imports.
- Stage24: exact arithmetic repeated-residue count R is running.
- Stage25: physical progression and bounded-order targets are in preflight.

Settings: gpt-6-astra / medium, proof concurrency ceiling 16, five attempts per node. Successful identical retrievals are cached with provenance within a run; retrieval requests are serialized to reduce rate-limit failures.

Full M5 is not yet formally verified. The complete polynomial inclusion-exclusion and counting/reconstruction chain, final bounded construction and birth/later-order integration, and executable arithmetic refinements remain. The component count is not a percentage of the full theorem; no stronger mathematical goal has been substituted.
