import Family8Grounding.Family8PaperFullCanonicalGroundingV496
import Family8Grounding.Family8StickySelectedFiberLowCFScalarEnvelopeV4

/-!
# Full canonical grounding checkpoint V497

Adds the retained-parent low-CF scalar envelope: the exact local source
constant and normalized proxy constant are finite, both are bounded by an
explicit selected-card envelope, and the literal proxy loss is dominated by
the corresponding closed-loss envelope.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV497

open Family8StickySelectedFiberLowCFScalarEnvelopeV4

#print axioms selectedFiberLowCFSourceConstant_ne_top
#print axioms selectedFiberLowCFSourceConstant_le_cardEnvelope
#print axioms selectedFiberLowCF_normalizedConstant_ne_top
#print axioms selectedFiberLowCF_normalizedConstant_le_cardEnvelope
#print axioms selectedFiberLowCF_proxyClosedLoss_le_cardEnvelope

end Family8PaperFullCanonicalGroundingV497
