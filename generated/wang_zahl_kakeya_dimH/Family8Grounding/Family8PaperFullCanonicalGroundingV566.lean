import Family8Grounding.Family8PaperFullCanonicalGroundingV565
import Family8Grounding.Family8CanonicalGraphFrozenExplicitTruncationFinalRetentionV1
import Family8Grounding.Family8VerticalGraphCBucketLossPowerV1
import Family8Grounding.Family8CanonicalGraphFrozenUniformFullBallPositiveCarrierAlignmentV1

/-!
# Full canonical grounding interface checkpoint V566

This checkpoint closes the adaptive fibre-scale selection seam recorded in
V565.  The canonical graph is truncated at the explicit level
`densityFloor * tau / 96`; the low-fibre tail is paid geometrically, at least
half of the projected source mass remains, and exact-card selection is then
performed on that same high-fibre set.  The resulting retention-and-ceiling
bound has literal loss `4 * graph.card * p` and contains no posterior
`ell`-dependent or dyadic-scale loss.

The literal vertical graph-bucket count also now has an `O(tau⁻¹)` bound and
a small-delta power wrapper.  The fixed-ball raw/positive-carrier seam is
transported without loss.

This checkpoint does not claim that Family8 is closed.  The remaining
terminal obligation is the fixed-witness payment (or an equivalent global
calibration) relating the endpoint/local restricted mass to the same
canonical graph selection.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV566

#print axioms
  Family8CanonicalGraphFrozenExplicitTruncationFinalRetentionV1.exists_sameGraph_explicitLevel_exactCard_retention_and_ceiling
#print axioms
  Family8VerticalGraphCBucketLossPowerV1.three_mul_verticalGraphCBucketLoss_halfScale_le_deltaPower_of_constant
#print axioms
  Family8CanonicalGraphFrozenUniformFullBallPositiveCarrierAlignmentV1.sameGraphUniformFullBallWitnessAlignment_of_fixedBallRestrictedShadingMassPayment

end Family8PaperFullCanonicalGroundingV566
