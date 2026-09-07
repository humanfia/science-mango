import Family8Grounding.Family8EndpointFirstCrossingIdentityFirstTransportV3
import Family8Grounding.Family8FrozenComparableLogLossSourceCardTransferV2
import Family8Grounding.Family8NormalizedCrossingFrozenComparableAdapterV3
import Family8Grounding.Family8NormalizedCrossingSourceTauShadingV2
import Family8Grounding.Family8NormalizedFirstCrossingFullRefinementAssemblyV1
import Family8Grounding.Family8ParameterLadderV1
import FamilyStickyGrounding.FamilyStickyScaleChainCappedSeedSequenceV2
import FamilyStickyGrounding.FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
import Mathlib.Tactic

/-!
# Endpoint FirstCrossing frozen loss as an arbitrary source-scale power, V3

The buffered lower family is reindexed, but on the identity coherent cover
its lower index cardinal is exactly the original datum cardinal.  Thus the
clean source-card transfer theorem absorbs the literal active frozen loss.
One additional fixed threshold absorbs the coefficient four used by the
singleton middle.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8EndpointFirstCrossingIdentityFrozenLossPowerV3

open Family8ActiveFrozenComparableLogLossAbsorptionV4
open Family8EndpointFirstCrossingIdentityFirstTransportV3
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableLogLossSourceCardTransferV2
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCrossingFrozenComparableAdapterV3
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- Uniform threshold absorbing both the active frozen logarithmic loss and
the fixed coefficient four. -/
def endpointFirstCrossingFrozenLossFourThreshold
    (lossExponent : Real) : NNReal :=
  min (activeFrozenComparableLossAbsorptionThreshold (lossExponent / 2))
    (finiteConstantSmallDeltaThreshold 4 (lossExponent / 2))

theorem endpointFirstCrossingFrozenLossFourThreshold_pos
    (lossExponent : Real) :
    0 < endpointFirstCrossingFrozenLossFourThreshold lossExponent := by
  exact lt_min (activeFrozenComparableLossAbsorptionThreshold_pos _)
    (finiteConstantSmallDeltaThreshold_pos _ _)

/-- The literal source loss in the endpoint exact-outer certificate, times
four, is bounded by any prescribed positive source-scale power. -/
theorem endpointFirstCrossing_frozenLoss_mul_four_le_rpow
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : FirstActualNormalizedCrossingWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num)))
      P.epsilon P.epsilon_pos.le P.eta P.N)
    {lossExponent : Real} (hlossExponent : 0 < lossExponent)
    (hsmall : delta <=
      endpointFirstCrossingFrozenLossFourThreshold lossExponent) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let G := bufferedIntervalCover E hE C S P.epsilon
      P.epsilon_pos.le W.m W.rho W.buffered
    (frozenComparableLoss {i // i ∈ G.activeFine}
        (Fin G.activeCoarse.card) : ENNReal) * 4 <=
      (delta : ENNReal) ^ (-lossExponent) := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let G := bufferedIntervalCover E hE C S P.epsilon
    P.epsilon_pos.le W.m W.rho W.buffered
  have hindex :
      Fintype.card (bufferedLowerIndex E C S W.m) <=
        Fintype.card index := by
    simp only [bufferedLowerIndex, C,
      identityRadiusCoherentCover, identityRadiusScaleCover,
      Fintype.card_fin]
    exact le_rfl
  have hloss :
      (frozenComparableLoss {i // i ∈ G.activeFine}
          (Fin G.activeCoarse.card) : ENNReal) <=
        (delta : ENNReal) ^ (-(lossExponent / 2)) := by
    exact activeFrozenComparableLoss_le_rpow_of_indexCard_le_source
      D hD G hindex (by positivity)
        (hsmall.trans (min_le_left _ _))
  have hfour : (4 : ENNReal) <=
      (delta : ENNReal) ^ (-(lossExponent / 2)) := by
    exact finiteConstant_le_delta_negativePower
      (by norm_num) (by positivity) hD.delta_pos
        (hsmall.trans (min_le_right _ _))
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  calc
    (frozenComparableLoss {i // i ∈ G.activeFine}
        (Fin G.activeCoarse.card) : ENNReal) * 4 <=
      (delta : ENNReal) ^ (-(lossExponent / 2)) *
        (delta : ENNReal) ^ (-(lossExponent / 2)) :=
      mul_le_mul' hloss hfour
    _ = (delta : ENNReal) ^ (-lossExponent) := by
      rw [<- ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
      congr 1
      ring

#print axioms endpointFirstCrossingFrozenLossFourThreshold_pos
#print axioms endpointFirstCrossing_frozenLoss_mul_four_le_rpow

end
end Family8EndpointFirstCrossingIdentityFrozenLossPowerV3
