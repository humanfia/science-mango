# Stage 9 results — integer Mobius connectivity indicator

All four frozen targets passed on their first attempts and passed combined Lean compilation and axiom checks. Completed batches 1–6 and 9 contain 41 unique accepted lemmas.

For positive N and any finite supports A,B, the sum of mu(d) over d dividing N and every support exponent is exactly 1 when gcd(N,A,B)=1 and 0 otherwise. The proof identifies the filtered divisor set with the divisors of the support gcd and applies the library Mobius convolution identity. Empty supports and zero exponents are covered; N>0 is the original order-domain assumption.

The polynomial inclusion-exclusion factor and its combination with character counts remain separate obligations.

[Assembled proof](experiment/AcceptedExperiment.lean), [acceptance receipt](experiment/result.json), [status DAG](experiment/GRAPH.md).
