# Stage 5 results — bounded CRT connectivity repair

All five frozen targets passed on their first attempts and passed combined Lean compilation and axiom acceptance. Total accepted individual lemmas through this stage: 30.

The final theorem states: for positive δ and T, gcd(gcd(T,δ),e)=1 implies existence of k with w≤k<w+δ and gcd(δ,e+kT)=1. The proof uses safe local residues 0 or 1, CRT over distinct prime divisors, an interval representative, and the prime-divisor characterization of coprimality. It includes δ=1 and the prime 2.

This discharges the bounded arithmetic repair lemma at the original bound. Integration with actual packed supports and their complete polynomial signature remains a separate obligation.

[Assembled proof](experiment/AcceptedExperiment.lean), [acceptance receipt](experiment/result.json), [status DAG](experiment/GRAPH.md).
