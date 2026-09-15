# Original M6 recipe isometries

This batch formalizes the three transformations in PROOF.md §9: independent cyclic translations of the two recipe blocks, a common unit permutation of cyclic indices, and exchange of blocks. The exact conclusions transport membership in the existing actual `M6.Spaces.B` and `M6.Spaces.C` and preserve physical Hamming weight. The common multiplier is a unit of `ZMod N`, acting on exponents; it is not arbitrary polynomial multiplication.

Seventeen frozen targets use thirty verified existing physical/flatten/space proofs. Definitions and exact target types passed preflight, with empty contexts and no pending dependency. The final three theorems instantiate the generic transport helper and have no free isometry-oracle hypothesis. They cover every positive N, including N=1 and composite/even N. No span invariance, classification, or module shear is asserted. R=0 formulas are handled by the root agent separately.

Live proof search uses gpt-6-astra medium, concurrency cap 16, five attempts, and the existing Mathlib plus Physlib retrieval and exact-type/axiom/compiler acceptance gates. Definitions and targets are frozen before launch.
