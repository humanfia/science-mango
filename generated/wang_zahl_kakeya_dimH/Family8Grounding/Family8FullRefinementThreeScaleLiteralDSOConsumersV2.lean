import Family8Grounding.Family8EndpointIdentityDividingScaleOutputOrchestrationV4
import Family8Grounding.Family8FirstActualCrossingFullRefinementCountLossCompositionV2
import Family8Grounding.Family8FullRefinementActualDatumV1
import Family8Grounding.Family8NormalizedLongIntervalCoreArbitraryMiddleCountLossCompositionV1

/-!
# Literal DSO consumers for the two full-refinement three-scale branches, V2

The stopping witnesses live on `fullRefinementDatum D`, while the final
datum-level output is stated for `D`.  These endpoints perform exactly that
definitional transport and inject the resulting three-scale estimate into
the right branch of `DividingScaleOutput`.

V1 omitted several namespaces used in the public signatures and is not
imported.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8FullRefinementThreeScaleLiteralDSOConsumersV2

open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma targetEpsilon : Real}

/-- The long-core count-loss endpoint, transported from the literal full
refinement back to the source datum and injected into `DividingScaleOutput`.
-/
theorem longCore_dividingScaleOutput_of_threeScaleCountComparison
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    {middleScale : NNReal}
    (hTauMiddle : S.tau W.m ≤ middleScale)
    {firstCount middleCount thirdCount : Nat}
    {countLoss : ENNReal}
    (hTargetEpsilon : 0 < targetEpsilon)
    (hGammaOne : gamma ≤ 1)
    (hcount :
      ((firstCount * (middleCount * thirdCount) : Nat) : ENNReal) ≤
        countLoss * (Fintype.card index : ENNReal))
    (hsmall : delta ≤
      sectionEightThreeScaleActualThreshold gamma
        (targetEpsilon / 4))
    {firstAverage middleAverage thirdAverage : ENNReal}
    {firstLoss thirdLoss : ENNReal}
    (hTriple : D.shading.averageMultiplicity ≤
      firstAverage * (middleAverage * thirdAverage))
    (hFirst : firstAverage ≤ firstLoss *
      sectionEightScaleCountFrostmanFactor
        delta (S.tau W.m) firstCount gamma)
    (hMiddle : middleAverage ≤
      (delta : ENNReal) ^ (10 * P.eta W.stage) *
        sectionEightScaleCountFrostmanFactor
          (S.tau W.m) middleScale middleCount gamma)
    (hThird : thirdAverage ≤ thirdLoss *
      sectionEightScaleCountFrostmanFactor
        middleScale 1 thirdCount gamma)
    (hAggregateLoss :
      (firstLoss * thirdLoss) * countLoss ^ (1 - gamma / 2) ≤
        (delta : ENNReal) ^ (-3 * P.eta W.stage)) :
    DividingScaleOutput D P targetEpsilon := by
  right
  have hTripleFull :
      (fullRefinementDatum D).shading.averageMultiplicity ≤
        firstAverage * (middleAverage * thirdAverage) := by
    simpa only [fullRefinementDatum_averageMultiplicity] using hTriple
  have hOutput :=
    Family8NormalizedLongIntervalCoreArbitraryMiddleCountLossCompositionV1.NormalizedLongIntervalCoreWitness.exists_stage_outerLoss_of_arbitraryMiddleCountComparison
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      C S P W hTauMiddle hTargetEpsilon hGammaOne hcount hsmall
      hTripleFull hFirst hMiddle hThird hAggregateLoss
  simpa only [fullRefinementDatum_averageMultiplicity,
    fullRefinementDatum_actualFamilyVolume] using hOutput

/-- The first-crossing count-loss endpoint already concludes on the source
datum; this theorem injects it into the literal DSO expected by the endpoint
selector.
-/
theorem firstCrossing_dividingScaleOutput_of_threeScaleCountComparison
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : FirstActualNormalizedCrossingWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
        C S P.epsilon P.epsilon_pos.le P.eta P.N)
    {firstCount middleCount thirdCount : Nat}
    {countLoss : ENNReal}
    (hTargetEpsilon : 0 < targetEpsilon)
    (hGammaOne : gamma ≤ 1)
    (hcount :
      ((firstCount * (middleCount * thirdCount) : Nat) : ENNReal) ≤
        countLoss * (Fintype.card index : ENNReal))
    (hsmall : delta ≤
      sectionEightThreeScaleActualThreshold gamma
        (targetEpsilon / 4))
    {firstAverage middleAverage thirdAverage : ENNReal}
    {firstLoss thirdLoss : ENNReal}
    (hTriple : D.shading.averageMultiplicity ≤
      firstAverage * (middleAverage * thirdAverage))
    (hFirst : firstAverage ≤ firstLoss *
      sectionEightScaleCountFrostmanFactor
        delta (S.tau W.m) firstCount gamma)
    (hMiddle : middleAverage ≤
      (delta : ENNReal) ^ (10 * P.eta W.stage) *
        sectionEightScaleCountFrostmanFactor
          (S.tau W.m) W.rho middleCount gamma)
    (hThird : thirdAverage ≤ thirdLoss *
      sectionEightScaleCountFrostmanFactor
        W.rho 1 thirdCount gamma)
    (hAggregateLoss :
      (firstLoss * thirdLoss) * countLoss ^ (1 - gamma / 2) ≤
        (delta : ENNReal) ^ (-3 * P.eta W.stage)) :
    DividingScaleOutput D P targetEpsilon := by
  right
  exact
    Family8FirstActualCrossingFullRefinementCountLossCompositionV2.FirstActualNormalizedCrossingWitness.exists_stage_outerLoss_of_threeScaleCountComparison
      D hD C S P W hTargetEpsilon hGammaOne hcount hsmall
      hTriple hFirst hMiddle hThird hAggregateLoss

#print axioms longCore_dividingScaleOutput_of_threeScaleCountComparison
#print axioms firstCrossing_dividingScaleOutput_of_threeScaleCountComparison

end
end Family8FullRefinementThreeScaleLiteralDSOConsumersV2
