import Family8Grounding.Family8PaperFullCanonicalGroundingV499
import Family8Grounding.Family8ENNRealLossStrictMiddleCompositionV2

/-!
# Full canonical grounding checkpoint V500

Adds the strict literal middle-factor composition.  It keeps the honest
ENNReal selection loss and the literal selected-cardinality, and absorbs the
remaining coefficient and relative-scale gain into the required global
`delta ^ (10 * eta)` factor.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV500

open Family8ENNRealLossStrictMiddleCompositionV2

#print axioms four_mul_sourceAverage_le_globalPower_mul_sectionEight

end Family8PaperFullCanonicalGroundingV500
