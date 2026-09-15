# Stage 18: subset exclusions as factor-product divisibility

Reviewed M5 section 3 uses inclusion-exclusion over distinct remaining irreducible factors. This batch supplies the algebraic bridge: for a finite set S of monic irreducibles and F nonzero dividing A, simultaneous events F*p dividing A for every p in S are equivalent to F*product(S) dividing A. Applying the same result to a and b supplies the joint event required by the count.

The five targets establish distinct-factor coprimality, product divisibility, common-factor cancellation, their assembled equivalence, and the cyclic-cap statement for subsets of normalizedFactors(M_N/F). Every multiplicity in F and the cyclic quotient remains present. Neither F nor M_N is assumed squarefree, and F may share factors with S. The empty subset is included: the hypothesis F|A supplies its event. A=0 is permitted.

Pinned Mathlib APIs include Irreducible.coprime_iff_not_dvd, Polynomial.eq_of_monic_of_associated, Finset.prod_dvd_of_coprime, Finset.dvd_prod_of_mem, EuclideanDomain.dvd_div_of_mul_dvd and EuclideanDomain.mul_div_cancel'. The optional cyclic-cap target uses normalized-factor irreducibility/divisibility and the verified stage12 binary_monic proof. The exact accepted stage12 promotion and its binary_dvd_antisymm companion are imported unchanged, with receipts; other sources match the immutable52 import snapshot.

All target contexts are empty; GraphPreflight.lean is generated directly from graph.json. These are targets and a checked dependency environment, not accepted stage18 proofs. Polynomial Möbius counting and full M5 remain separate obligations.
