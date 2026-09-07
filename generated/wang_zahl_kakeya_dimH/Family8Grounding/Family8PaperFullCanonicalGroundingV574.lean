import Family8Grounding.Family8PaperFullCanonicalGroundingV573
import Family8Grounding.Family8AllSlabRowPowerAlgebraV1
import Family8Grounding.Family8AverageMultiplicityToUnionLowerV1
import Family8Grounding.Family8PlankFixedThetaAllSlabMassWeightedEq43ProducerV1

/-!
# Full canonical grounding interface checkpoint V574

The fixed-theta all-slab route now contains the exact row-dependent power
cancellation used after Equation (43).  A row may pay its actual restriction
loss `globalMass / rowMass`; after affine-Jacobian weighting the row mass is
linear, so the exact row partition sums to the global `beta / 2` power.  No
uniform row lower bound, equal-row-mass hypothesis, or artificial comparison
between the Frostman constant and the branching number is imposed.

The reverse multiplicity-to-union adapter is also available: an actual
Family 7 average-multiplicity upper bound and a row shading-mass floor produce
the normalized row-union lower bound without extra positivity or finiteness
assumptions on the multiplicity cap.

The endpoint Equation (32) wrapper imported from V573 has additionally been
reviewed and weakened: active-parent admissibility is now derived internally
from the original admissible datum.

Family 8 is still open on constructing the concrete fixed-theta row geometry
and rowwise Equation (43)/Family 7 inputs, and on the large-width Lemma 6.9
scalar branch plus the final parameter ledger.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV574

#print axioms
  Family8AllSlabRowPowerAlgebraV1.allSlab_rowPower_identity
#print axioms
  Family8AllSlabRowPowerAlgebraV1.allSlab_weighted_rowLower
#print axioms
  Family8AverageMultiplicityToUnionLowerV1.massFloor_div_cap_le_volume_shadedUnion_of_averageMultiplicity_le
#print axioms
  Family8PlankFixedThetaAllSlabMassWeightedEq43ProducerV1.FixedThetaAllSlabRawRowDependentEq43Certificate.toMassWeightedEq43Certificate
#print axioms
  Family8PlankFixedThetaAllSlabMassWeightedEq43ProducerV1.FixedThetaAllSlabRawRowDependentEq43Certificate.halfPower_le_weightedRows
#print axioms
  Family8WinnerSideJointBucketEndpointPackedEq32LossAwarePaymentV1.endpointIdentityLossAwareEq32Payment_of_winnerSide_jointBucket_at

end Family8PaperFullCanonicalGroundingV574
