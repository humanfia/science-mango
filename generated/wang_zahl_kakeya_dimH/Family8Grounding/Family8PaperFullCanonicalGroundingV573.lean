import Family8Grounding.Family8PaperFullCanonicalGroundingV572
import Family8Grounding.Family8WinnerSideOuterInnerLabelScaleRelationV1
import Family8Grounding.Family8WinnerSideJointBucketEndpointPackedEq32ConsumerV1
import Family8Grounding.Family8WinnerSideJointBucketEndpointPackedEq32LossPowerV1
import Family8Grounding.Family8WinnerSideJointBucketEndpointPackedEq32LossAwarePaymentV1
import Family8Grounding.Family8AllSlabUnionCancellationBudgetV1
import Family8Grounding.Family8PlankFixedThetaAllSlabRowsV1
import Family8Grounding.Family8PlankFixedThetaAllSlabAssemblyV1
import Family8Grounding.Family8HRowFreshForwardPowerGateV1
import Family8Grounding.Family8HRowFreshSquareCardinalityEndpointV1

/-!
# Full canonical grounding interface checkpoint V573

The literal winner-side joint bucket now reaches the packed two-label
Equation (32) consumer with the actual outer and occupied inner labels.  Its
automatic source-retention ledger displays both frozen-comparability factors,
and the terminal loss-aware wrapper pays the coefficient and geometry losses
with the exact exponent `1 - gamma / 2`.  The terminal wrapper uses unit
`countLoss`; the second frozen factor has already been paid by the source
transport and is not counted twice.

On the Family 7 side, the fixed-theta all-slab decomposition now has exact
row mass partition and union identities, together with a mass-weighted
Equation (43) aggregation interface and a proved Jacobian/overlap assembly.
The honest high/low H-row gate is also recorded without imposing the false
global inequality that the effective loss is bounded by the selected
branching number.

Family 8 remains open.  The unresolved inputs are the genuine fixed-theta
Family 7 analytic row lower and its geometric producer, the large-width
Lemma 6.9 scalar payment, and their final branch/parameter ledger.  This
checkpoint records only compiled infrastructure and makes no closure claim.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV573

#print axioms
  Family8WinnerSideOuterInnerLabelScaleRelationV1.winnerSide_outerInnerLabelScaleRelation
#print axioms
  Family8WinnerSideJointBucketEndpointPackedEq32ConsumerV1.winnerSide_jointBucket_endpointPackedEq32_at
#print axioms
  Family8WinnerSideJointBucketEndpointPackedEq32LossPowerV1.jointWinnerSide_endpointPackedAutomaticSourceLoss_le_rpow
#print axioms
  Family8WinnerSideJointBucketEndpointPackedEq32LossAwarePaymentV1.endpointIdentityLossAwareEq32Payment_of_winnerSide_jointBucket_at
#print axioms
  Family8PlankFixedThetaAllSlabRowsV1.FixedThetaAllSlabRows.familyVolume_eq_sum_rowFamily_familyVolume
#print axioms
  Family8PlankFixedThetaAllSlabAssemblyV1.FixedThetaAllSlabRowMassWeightedEq43Certificate.aggregate_rows_lower
#print axioms
  Family8PlankFixedThetaAllSlabAssemblyV1.FixedThetaAllSlabJacobianOverlapCertificate.weighted_rows_le_global
#print axioms
  Family8PlankFixedThetaAllSlabAssemblyV1.FixedThetaAllSlabEq43RowsLowerCertificate.localCore_le_globalCoarse
#print axioms
  Family8HRowFreshForwardPowerGateV1.hRowFresh_forwardPowerBudget_or_lowForwardBranch
#print axioms
  Family8HRowFreshForwardPowerGateV1.hRowFresh_actualThirdAverage_le_of_lowForwardBranch_and_rowMassBudget
#print axioms
  Family8HRowFreshSquareCardinalityEndpointV1.hRowFresh_actualThirdAverage_le_sourceCardProp66Factor_of_correlationPower

end Family8PaperFullCanonicalGroundingV573
