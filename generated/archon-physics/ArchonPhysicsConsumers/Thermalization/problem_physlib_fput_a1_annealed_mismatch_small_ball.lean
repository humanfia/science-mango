import ArchonPhysics.PhyslibFPUTA1AnnealedMismatchSmallBall

/-!
# Consumer: actual A1 mismatch small balls under frozen iid masses

This consumer records the exact boundary of the new finite-volume result.
The unconditional statements provide the actual ordered-frequency mismatch
law, the coefficient ceiling, the reduction of annealed near coefficient mass
to finitely many mismatch probabilities, and the exact pair/complement random
variable reconstruction.

The sharp small-ball conclusion has no premise saying that a near-resonant
set is small.  Its model-facing premise instead spells out the missing fact:
on a selected mass fiber the actual mismatch must be injective and have
Jacobian determinant at least `jacLower`.  The good-set theorem displays the
complement mass if that fails globally.  Thus coefficient zeros and Jacobian
zeros are not conflated.

The law here is the initial frozen iid mass law.  Initial Haar/Gaussian phases
do not enter, and no Markov property, block independence, re-Haar mechanism,
`g,N` joint limit, kinetic time window, mismatch equidistribution, or vanishing
memory/recollision remainder is asserted.  Those are separate prerequisites
for a Deng--Hani-type kinetic closure.  The one-denominator endpoint is meant
to be used once for every cumulative denominator in the already finite
ordered/branching history enumeration.
-/

open ArchonPhysics.PhyslibFPUTA1AnnealedMismatchSmallBall

#check measurable_physlibA1MismatchSample
#check physlibA1MismatchLaw_Ioo
#check card_quadraticPhaseTerm
#check physlibA1StaticCoefficient_le_two_absKappa_radiusSq
#check physlibA1AnnealedNearStaticAbsMass_le_sum_mismatchLaw
#check oneSiteMismatchSmallBall_le_sharp_add_badMass
#check physlibA1PairMismatchSmallBall_le_integrated_badMass
#check physlibA1PairMismatchSmallBall_of_fullTransversality
#check physlibA1ReconstructedMismatchChart_ensemble_eq
#check physlibA1MismatchLaw_smallBall_of_uniform_pairFiberTransversality
#check physlibA1AnnealedNearStaticAbsMass_le_explicit_smallBall_of_uniform_pairFiberTransversality

#print axioms physlibA1AnnealedNearStaticAbsMass_le_sum_mismatchLaw
#print axioms oneSiteMismatchSmallBall_le_sharp_add_badMass
#print axioms physlibA1PairMismatchSmallBall_of_fullTransversality
#print axioms physlibA1ReconstructedMismatchChart_ensemble_eq
#print axioms physlibA1MismatchLaw_smallBall_of_uniform_pairFiberTransversality
#print axioms
  physlibA1AnnealedNearStaticAbsMass_le_explicit_smallBall_of_uniform_pairFiberTransversality
