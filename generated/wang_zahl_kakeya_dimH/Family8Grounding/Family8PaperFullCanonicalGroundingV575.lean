import Family8Grounding.Family8PaperFullCanonicalGroundingV574
import Family8Grounding.Family8PlankFixedThetaAllSlabAggregateEq43ProducerV2

/-!
# Full canonical grounding interface checkpoint V575

This checkpoint replaces the common-row-base route as the canonical
fixed-theta Equation (43) interface.  The comparison loss is explicit, the
Family 7 base may vary from row to row, and the sole good-row/popularity input
is an aggregate base-weighted mass floor.  Thus membership in the all-slab
catalogue does not silently assert that every row is equally good.

The restriction loss and source Frostman constant occur together exactly
once under the negative exponent `-(1 - beta / 2)`.  The interface permits a
zero comparison loss and only requires the finiteness needed by ENNReal power
algebra.  The older common-base certificate imported through V574 remains a
compiled convenience specialization, but it is not the intended concrete
Family 7 route.

Family 8 remains open on producing the rowwise Equation (43), normalized
Family 7 bounds, and aggregate base-mass floor from the actual fixed-theta
geometry, together with the large-width Lemma 6.9 branch and final parameter
ledger.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV575

#print axioms
  Family8PlankFixedThetaAllSlabAggregateEq43ProducerV2.FixedThetaAllSlabRawAggregateEq43Certificate.weighted_row_lower
#print axioms
  Family8PlankFixedThetaAllSlabAggregateEq43ProducerV2.FixedThetaAllSlabRawAggregateEq43Certificate.aggregate_negativePower_le_weightedRows
#print axioms
  Family8PlankFixedThetaAllSlabAggregateEq43ProducerV2.FixedThetaAllSlabRawAggregateEq43Certificate.aggregateBase_halfPower_le_weightedRows

end Family8PaperFullCanonicalGroundingV575
