# Exact quotient subset arithmetic (source §2)

`M5.ArithmeticSubset.n P hP W k z` is an integer: its numerator is the sum over all binary-coordinate characters of `chi(z)` times the signed binomial convolution, divided by `2^P.natDegree`. Its definition does not enumerate subsets. `negativeCount` scans the exponent set W for negative monomial character values. The subset-filter cardinality appears only on the right side of the exact counting theorem.

Six frozen targets connect the formula to the previously accepted quotient and binomial results:

1. Every quotient character value is +1 or -1.
2. Coordinates of the quotient image of `ofSupport U` equal the sum of the monomial coordinates.
3. The explicit binomial term equals the signed-product coefficient, using stage11's accepted coefficient theorem.
4. The numerator equals `2^degree` times the exact k-subset residue count, using stage14's generic subset character count instantiated at the quotient monomial coordinates.
5. Exact integer division yields `n = count`.
6. Hence n is nonnegative.

The first two nodes can run independently; the third depends only on the first. The fourth waits for nodes two and three and uses the now accepted stage14 subset-count theorem. The fifth and sixth follow sequentially. All five stage14 proofs in its dependency closure were promoted with receipt/payload/source/target verification; the original pending gate was discharged by that accepted import. No stage14 theorem is reproved by this preparation.

Only monicity of P is assumed. The statements include P=1, W empty, k=0, k>|W|, and all quotient collisions/cancellations. k has type Nat; the source's convention for negative indices is an external extension, not an additional hypothesis or a claim proved here. Definitions currently use the existing noncomputable quotient coordinate infrastructure; the target is the arithmetic identity, not an executable algorithm refinement.

The project imports the immutable, hash-verified 72-lemma checkpoint and the five accepted stage14 proofs with their definitions. `GraphPreflight.lean` declares the six propositions as definitions and checks their types; it contains no new theorem proofs, sorry, or axioms. Preflight success is not theorem acceptance.
