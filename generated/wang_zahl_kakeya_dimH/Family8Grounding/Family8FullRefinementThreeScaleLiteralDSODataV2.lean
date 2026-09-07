import Family8Grounding.Family8FullRefinementThreeScaleLiteralDSOConsumersV2

/-!
# Stable data packages for the two literal three-scale DSO consumers, V2

The long-core and first-crossing endpoints each consume a dependent family of
counts, averages, and loss inequalities.  These records freeze every member of
that family on one literal witness.  V1 omitted the threshold namespace and is
not imported.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8FullRefinementThreeScaleLiteralDSODataV2

open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8FullRefinementActualDatumV1
open Family8FullRefinementThreeScaleLiteralDSOConsumersV2
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

/-- All same-object numerical data needed by the literal long-core DSO
consumer. -/
structure LongCoreThreeScaleDSOData
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    (targetEpsilon : Real) where
  middleScale : NNReal
  hTauMiddle : S.tau W.m ≤ middleScale
  firstCount : Nat
  middleCount : Nat
  thirdCount : Nat
  countLoss : ENNReal
  hCount :
    ((firstCount * (middleCount * thirdCount) : Nat) : ENNReal) ≤
      countLoss * (Fintype.card index : ENNReal)
  hSmall : delta ≤
    sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4)
  firstAverage : ENNReal
  middleAverage : ENNReal
  thirdAverage : ENNReal
  firstLoss : ENNReal
  thirdLoss : ENNReal
  hTriple : D.shading.averageMultiplicity ≤
    firstAverage * (middleAverage * thirdAverage)
  hFirst : firstAverage ≤ firstLoss *
    sectionEightScaleCountFrostmanFactor
      delta (S.tau W.m) firstCount gamma
  hMiddle : middleAverage ≤
    (delta : ENNReal) ^ (10 * P.eta W.stage) *
      sectionEightScaleCountFrostmanFactor
        (S.tau W.m) middleScale middleCount gamma
  hThird : thirdAverage ≤ thirdLoss *
    sectionEightScaleCountFrostmanFactor
      middleScale 1 thirdCount gamma
  hAggregateLoss :
    (firstLoss * thirdLoss) * countLoss ^ (1 - gamma / 2) ≤
      (delta : ENNReal) ^ (-3 * P.eta W.stage)

/-- Consume a stable long-core data package on exactly the objects used to
construct it. -/
theorem LongCoreThreeScaleDSOData.toDividingScaleOutput
    {D : ActualTubeDatum delta index} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family}
    {S : FiniteScaleSequence delta depth}
    {P : ParameterLadder epsilon0 beta gamma}
    {W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S}
    {targetEpsilon : Real}
    (X : LongCoreThreeScaleDSOData D hD C S P W targetEpsilon)
    (hTargetEpsilon : 0 < targetEpsilon) (hGammaOne : gamma ≤ 1) :
    DividingScaleOutput D P targetEpsilon :=
  longCore_dividingScaleOutput_of_threeScaleCountComparison
    D hD C S P W X.hTauMiddle hTargetEpsilon hGammaOne
      X.hCount X.hSmall X.hTriple X.hFirst X.hMiddle X.hThird
        X.hAggregateLoss

/-- All same-object numerical data needed by the literal first-crossing DSO
consumer. -/
structure FirstCrossingThreeScaleDSOData
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : FirstActualNormalizedCrossingWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
        C S P.epsilon P.epsilon_pos.le P.eta P.N)
    (targetEpsilon : Real) where
  firstCount : Nat
  middleCount : Nat
  thirdCount : Nat
  countLoss : ENNReal
  hCount :
    ((firstCount * (middleCount * thirdCount) : Nat) : ENNReal) ≤
      countLoss * (Fintype.card index : ENNReal)
  hSmall : delta ≤
    sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4)
  firstAverage : ENNReal
  middleAverage : ENNReal
  thirdAverage : ENNReal
  firstLoss : ENNReal
  thirdLoss : ENNReal
  hTriple : D.shading.averageMultiplicity ≤
    firstAverage * (middleAverage * thirdAverage)
  hFirst : firstAverage ≤ firstLoss *
    sectionEightScaleCountFrostmanFactor
      delta (S.tau W.m) firstCount gamma
  hMiddle : middleAverage ≤
    (delta : ENNReal) ^ (10 * P.eta W.stage) *
      sectionEightScaleCountFrostmanFactor
        (S.tau W.m) W.rho middleCount gamma
  hThird : thirdAverage ≤ thirdLoss *
    sectionEightScaleCountFrostmanFactor
      W.rho 1 thirdCount gamma
  hAggregateLoss :
    (firstLoss * thirdLoss) * countLoss ^ (1 - gamma / 2) ≤
      (delta : ENNReal) ^ (-3 * P.eta W.stage)

/-- Consume a stable first-crossing data package on exactly the objects used
to construct it. -/
theorem FirstCrossingThreeScaleDSOData.toDividingScaleOutput
    {D : ActualTubeDatum delta index} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family}
    {S : FiniteScaleSequence delta depth}
    {P : ParameterLadder epsilon0 beta gamma}
    {W : FirstActualNormalizedCrossingWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
        C S P.epsilon P.epsilon_pos.le P.eta P.N}
    {targetEpsilon : Real}
    (X : FirstCrossingThreeScaleDSOData D hD C S P W targetEpsilon)
    (hTargetEpsilon : 0 < targetEpsilon) (hGammaOne : gamma ≤ 1) :
    DividingScaleOutput D P targetEpsilon :=
  firstCrossing_dividingScaleOutput_of_threeScaleCountComparison
    D hD C S P W hTargetEpsilon hGammaOne X.hCount X.hSmall
      X.hTriple X.hFirst X.hMiddle X.hThird X.hAggregateLoss

#print axioms LongCoreThreeScaleDSOData
#print axioms LongCoreThreeScaleDSOData.toDividingScaleOutput
#print axioms FirstCrossingThreeScaleDSOData
#print axioms FirstCrossingThreeScaleDSOData.toDividingScaleOutput

end
end Family8FullRefinementThreeScaleLiteralDSODataV2
