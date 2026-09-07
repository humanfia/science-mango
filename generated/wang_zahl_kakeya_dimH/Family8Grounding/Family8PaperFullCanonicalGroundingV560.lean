import Family8Grounding.Family8PaperFullCanonicalGroundingV559
import Family8Grounding.Family8SelectedOccurrenceNormalizedCanonicalGlobalDeltaEq45ControlV1
import Family8Grounding.Family8HonestEq45CoupledThickAspectComparisonV1
import Family8Grounding.Family8SelectedOccurrenceOuterFamilyVolumeV1
import Family8Grounding.Family8SelectedOuterCanonicalDeltaScalarCancellationV1
import Family8Grounding.Family8SelectedOccurrenceNormalizedOuterScaleBridgeV1
import Family8Grounding.Family8SelectedOccurrenceActualParentLocalKatzTaoProducerV1
import Family8Grounding.Family8SelectedOccurrenceFrozenSameQPositiveCarrierCrossComposerV1
import Family8Grounding.Family8SelectedOccurrenceFrozenSameQPositiveCarrierScaledProductV1

/-!
# Full canonical grounding interface checkpoint V560

This checkpoint records two honest advances beyond V559.

First, the selected normalized outer family now has an exact canonical global
Delta construction, an exact outer-family volume identity, and the coupled
`thickM * aspectRatio` comparison used to expose rather than hide the remaining
global concentration loss.  The normalized outer scale floor is also explicit.

Second, the same-`q`, same-label positive-carrier route now has a compiled
cross-multiplied Equation (46) interface and a compiled scaled outer/inner
product.  The common source factor is deliberately retained.  Actual-parent
owner fibres also inherit source-parent Katz--Tao control without `R.card` or
fibre-card loss.

This is not the final Family8 closure.  In particular, V560 does not assert a
producer for the selected-label scale reserve, the large-`b` terminal, the
rescaled outer-density floor, or cancellation of the complete source factor.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV560

#print axioms
  Family8SelectedOccurrenceActualParentLocalKatzTaoProducerV1.containedMassOn_actualParentOwner_le_sourceParentFiber
#print axioms
  Family8SelectedOccurrenceActualParentLocalKatzTaoProducerV1.ownerFiberIsKatzTao_of_sourceParentFibers_and_one_le_density
#print axioms
  Family8SelectedOccurrenceFrozenSameQPositiveCarrierCrossComposerV1.selectedOccurrenceFrozenSameQPositiveCarrier_sourceFactor_mul_finalFiberAverage_le_expandedEq46LHS
#print axioms
  Family8SelectedOccurrenceFrozenSameQPositiveCarrierScaledProductV1.sourceFactor_mul_sourceActiveFineAverage_le_four_mul_loss_mul_outer_mul_cross

end Family8PaperFullCanonicalGroundingV560
