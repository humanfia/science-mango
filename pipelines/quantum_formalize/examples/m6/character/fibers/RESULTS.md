# Exact fiber and dual-cardinality normalization accepted

All five targets succeeded on their first live attempts, with exact target, kernel and axiom checks. The combined assembly compiled and the project environment stayed unchanged. Canonical evidence is `experiment/` (99 manifest entries), from `dag-launcher-o7_pyf33`.

For arbitrary finite types and a function `L`, the proof first decomposes a sum of pulled-back polynomial weights into the sum over fibers. If every fiber has cardinality `k`, it proves

`∑ a, w (L a) = Polynomial.C (k : ℤ) * ∑ b, w b`.

It also proves `card(inputs) = k * card(outputs)`. These are exact integer-polynomial and natural-cardinality identities. They require the stated actual fiber sizes, but no additional positivity, surjectivity or squarefreeness assumption. The physical-map module supplies the actual `L` and its fiber-size theorem.

For a binary subspace `D` of `Fin m → ZMod 2`, a separate specialization of the accepted weighted MacWilliams formula proves

`(subspaceWords D).card * (dualWords D).card = 2^m`.

At constant coordinate weight 1, the local character product is `2^m` for the zero vector and zero for every nonzero vector. Since zero belongs to the actual subspace, only that contribution survives. Comparing polynomial constant coefficients gives the cardinality identity; no dimension, classification or nondegeneracy theorem was assumed.

The eight character-core imports were provenance-verified, recompiled and axiom-audited before this batch. All proofs use only `propext`, `Classical.choice` and `Quot.sound`. Settings remained `gpt-6-astra`, medium effort, concurrency 16, five rounds, with Mathlib and Physlib retrieval. These results provide the generic normalization steps used for the actual powers of two in M6; the final physical enumerator identities remain integration work.
