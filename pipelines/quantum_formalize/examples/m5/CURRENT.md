# Current M5 formalization progress

Stages 1–15 and 17–19 are complete: 96 named component lemmas accepted by Lean, with combined compilation per batch. The first 72 also passed a single integrated project and independent exact-type/axiom audit (integrated72). Integration of 90 components is running. These counts exclude the three accepted components in the incomplete stage16 batch.

New accepted components include exact subset and repeated-tuple character counts, finite Boolean inclusion-exclusion, distinct irreducible factor products with the residual cyclic cap, and the gcd/cutoff ingredients for the actual support repair. Original failure histories and successful repair provenance are retained.

Active:
- Stage16: repair the strict-divisor extra-factor proof and finish exact polynomial signature exclusion. Three accepted components are preserved.
- Stage20: exact arithmetic n(P,W,k,z) through the binomial/character formula; experiment running.
- Stage21: quotient congruence preserves complete signature, with packing and replacement applications; experiment running.
- Stage22: prepare the bounded connected support construction using accepted dependencies, with unfinished dependencies explicitly gated.

Settings: gpt-6-astra / medium, proof concurrency ceiling 16, five attempts per node. Successful identical retrievals are cached with provenance within a run; retrieval requests are serialized to reduce rate-limit failures.

Full M5 is not yet formally verified. The complete polynomial inclusion-exclusion and counting/reconstruction chain, final bounded construction and birth/later-order integration, and executable arithmetic refinements remain. The component count is not a percentage of the full theorem; no stronger mathematical goal has been substituted.
