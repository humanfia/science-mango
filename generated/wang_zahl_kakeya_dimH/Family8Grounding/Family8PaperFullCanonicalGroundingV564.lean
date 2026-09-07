import Family8Grounding.Family8PaperFullCanonicalGroundingV563
import Family8Grounding.Family8ProjectedActiveShadingMassQuantitativeExactCardFibreFloorV1
import Family8Grounding.Family8ProjectedActiveShadingMassQuantitativeDyadicFibreBucketV2

/-!
# Full canonical grounding interface checkpoint V564

This checkpoint freezes the weighted-mass-first replacement for the earlier
volume-only projected-band selection.  On one literal shading, active family,
projection and pair of windows, quantitative exact-card and lower-fibre-floor
selection now preserve a stated portion of projected shading mass.  A genuine
two-sided dyadic fibre bucket has a weighted-mass ceiling by
`2 * level * originalCard * planarVolume`; its bucket active pattern is only
required to be a subpattern of the positive exact-card pattern, so fibres at a
point are not incorrectly assumed to share one scale.

The remaining weighted seam is explicit: a finite dyadic pigeonhole must
produce a bucket satisfying the retained-mass premise of the final ceiling.
This checkpoint therefore records progress but does not claim the frozen-graph
tail budget or Family8 has closed.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV564

#print axioms
  Family8ProjectedActiveShadingMassQuantitativeExactCardFibreFloorV1.exists_exactCard_projectedActiveShadingMassBand_ge_average
#print axioms
  Family8ProjectedActiveShadingMassQuantitativeExactCardFibreFloorV1.exists_dyadic_fibreFloor_half_projectedMass_exactCardBand
#print axioms
  Family8ProjectedActiveShadingMassQuantitativeDyadicFibreBucketV2.dyadicFibreBucketWeightedMass_le_two_mul_level_mul_originalCard_mul_volume
#print axioms
  Family8ProjectedActiveShadingMassQuantitativeDyadicFibreBucketV2.sourceWeightedMass_div_loss_le_two_mul_level_mul_card_mul_volume

end Family8PaperFullCanonicalGroundingV564
