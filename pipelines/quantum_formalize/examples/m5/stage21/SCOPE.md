# Stage 21 scope

Section 5 first packs residue tuples, then replaces one exponent by an exponent congruent modulo `T`. The accepted packing and replacement lemmas already prove polynomial equality in `AdjoinRoot (cyclicModulus T)`. These four targets convert those equalities into equality of the exact complete signature `gcd(gcd(a,b), M_T)`.

The first target uses the quotient kernel to transfer divisibility by any divisor of `M_T`. The second applies that fact in both blocks and uses accepted binary polynomial divisibility antisymmetry. The final two specialize the result to literal occurrence packing and the existing support replacement definition.

Repeated factors and zero residue polynomials remain allowed. The algebraic statements also hold for `T = 0`: equality in the quotient by the zero polynomial implies ordinary equality. No root decomposition, squarefreeness, connectivity, or additional positivity assumption is introduced. Actual M5 realizations still require the original positive period and physical support hypotheses elsewhere.

This batch supplies the repaired-source signature identity, not the full bounded-source theorem. These files contain frozen specifications and type checks only; no new proofs are claimed.
