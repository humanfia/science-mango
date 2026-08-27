import ArchonPhysics.TruncatedGaussianFiniteDomination

/-!
# Consumer audit for finite-dimensional truncated-Gaussian domination

This file checks the one-coordinate, pair, arbitrary finite-product, `Fin 2`,
`Fin 6`, and exact-patch small-ball adapters.  It deliberately contains no
statement about domination or absolute continuity of infinite products.
-/

open ArchonPhysics
open ArchonPhysics.TruncatedGaussianFiniteDomination

#check continuous_gaussianPDFReal
#check exists_gaussianPDFReal_uniform_lower
#check restricted_volume_smul_le_restricted_gaussianReal
#check exists_coordinateLaw_domination
#check exists_iidMassPairLaw_domination
#check finitePi_smul_le_finitePi_of_smul_le
#check exists_finiteLaw_domination
#check exists_finiteLaw_two_domination
#check exists_finiteLaw_six_domination
#check pairFiniteLaw
#check exists_truncatedGaussian_linearSmallBallLower

#print axioms continuous_gaussianPDFReal
#print axioms exists_gaussianPDFReal_uniform_lower
#print axioms restricted_volume_smul_le_restricted_gaussianReal
#print axioms exists_coordinateLaw_domination
#print axioms exists_iidMassPairLaw_domination
#print axioms finitePi_smul_le_finitePi_of_smul_le
#print axioms exists_finiteLaw_domination
#print axioms exists_finiteLaw_two_domination
#print axioms exists_finiteLaw_six_domination
#print axioms exists_truncatedGaussian_linearSmallBallLower
