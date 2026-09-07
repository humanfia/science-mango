import Family8Grounding.Family8PaperFullCanonicalGroundingV548
import Family8Grounding.Family8TauActiveParentGreedyRetainedHighPrefixSplitV1
import Family8Grounding.Family8RestrictedSelectedMassOccupiedSameCoreSumV1
import Family8Grounding.Family8OccupiedSameCoreFiberLogWeightedSelectionV1
import Family8Grounding.Family8ArbitraryOccurrenceSameQCardBridgeV1
import Family8Grounding.Family8SameQSingletonExactRResidualV1
import Family8Grounding.Family8SameQSingletonFineBlockDensityNormalizedFrostmanV1

/-!
# Full canonical grounding interface checkpoint V549

The high route now retains the original factor-two first-hit mass before any
occurrence is chosen.  That selected mass is partitioned exactly over occupied
same-core occurrences, bucketed only by fibre-cardinality logarithm, and then
maximized inside the winning bucket.  Consequently the former linear
`occupied.card` loss is replaced by a logarithmic bucket loss while the bucket
cardinality is coupled to the same selected fibre and paid by the honest
product-count estimate.

For the resulting literal occurrence `q`, singleton exact-`R` density
normalization, Frostman control, and the local KT residual no longer require
canonical Proposition 5.1 membership or a density covering for unrelated
blocks.  The remaining work is the endpoint/Prop66 assembly of these compiled
pieces, not a new occurrence selection.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV549

#print axioms
  Family8RestrictedSelectedMassOccupiedSameCoreSumV1.restrictActualTubeDatum_shadingMass_eq_sum_occupied_sameCoreOccurrenceBlockShading
#print axioms
  Family8OccupiedSameCoreFiberLogWeightedSelectionV1.exists_occupiedCoreHighOccurrence_fiberLogBucket_weighted_sameQ
#print axioms
  Family8ArbitraryOccurrenceSameQCardBridgeV1.arbitraryOccurrence_card_mul_sameQ_fiberCard_le_two_mul_active
#print axioms
  Family8SameQSingletonExactRResidualV1.sameQ_singletonExactR_blockDensity_localKTResidual_dichotomy
#print axioms
  Family8SameQSingletonFineBlockDensityNormalizedFrostmanV1.sameQ_singletonFine_isFrostmanOn_of_sourceKatzTao

end Family8PaperFullCanonicalGroundingV549
