import Family8Grounding.Family8EndpointIdentityCoreSelectorV2
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Family8Grounding.Family8NormalizedLongIntervalCoreConsumerV1
import Family8Grounding.Family8StickyFiberContractedJohnSourcePowerEndpointV1
import FamilyStickyGrounding.FamilyStickyScaleChainCappedSeedSequenceV2
import FamilyStickyGrounding.FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
import Mathlib.Tactic

/-!
# Endpoint obstruction to the relative-scale contracted-John first factor

On the one-step endpoint sequence the long-core lower scale is exactly the
source scale.  Hence `delta / tau = 1`, while the fixed-constant absorption
threshold used by the relative-scale contracted-John endpoint is strictly
less than one for every positive absorption exponent.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8EndpointLongCoreContractedJohnFirstRatioNoGoV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8StickyFiberContractedJohnSourcePowerEndpointV1
open Family8StickyFiberContractedJohnSourcePowerEnvelopeV4
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-- The fixed contracted-John source threshold is genuinely below one. -/
theorem contractedJohnSourcePowerEndpointThreshold_lt_one
    {a : Real} (ha : 0 < a) :
    contractedJohnSourcePowerEndpointThreshold a < 1 := by
  have hconstant : 0 <
      contractedJohnSourceClosedLossFixedConstant.toNNReal := by
    apply ENNReal.toNNReal_pos
    · norm_num [contractedJohnSourceClosedLossFixedConstant]
    · norm_num [contractedJohnSourceClosedLossFixedConstant]
  have hbase : (1 : NNReal) <
      contractedJohnSourceClosedLossFixedConstant.toNNReal + 1 := by
    exact lt_add_of_pos_left 1 hconstant
  have hexponent : -(1 / a) < 0 := by
    have hinv : 0 < 1 / a := one_div_pos.mpr ha
    linarith
  have hclosed : contractedJohnSourceClosedLossThreshold a < 1 := by
    exact NNReal.rpow_lt_one_of_one_lt_of_neg hbase hexponent
  exact (min_le_left _ _).trans_lt hclosed

/-- Consequently the small-ratio premise of the contracted-John first bundle
cannot hold on any endpoint long-core witness. -/
theorem endpointLongCore_not_delta_div_tau_le_sourcePowerThreshold
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {epsilon0 beta gamma : Real}
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family (identityRadiusCoherentCover D.family)
        P.N P.epsilon P.eta
        (endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num))))
    {a : Real} (ha : 0 < a) :
    ¬ delta /
        (endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num))).tau W.m ≤
      contractedJohnSourcePowerEndpointThreshold a := by
  have hratio : delta /
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))).tau W.m = 1 := by
    rw [show W.m = (0 : Fin 1) from Subsingleton.elim _ _,
      endpointScaleSequence_tau_zero]
    exact div_self hD.delta_pos.ne'
  rw [hratio]
  exact not_le_of_gt (contractedJohnSourcePowerEndpointThreshold_lt_one ha)

#print axioms contractedJohnSourcePowerEndpointThreshold_lt_one
#print axioms endpointLongCore_not_delta_div_tau_le_sourcePowerThreshold

end
end Family8EndpointLongCoreContractedJohnFirstRatioNoGoV1
