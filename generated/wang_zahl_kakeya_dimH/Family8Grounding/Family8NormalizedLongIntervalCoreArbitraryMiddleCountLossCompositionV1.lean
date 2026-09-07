import Family8Grounding.Family8IdentifiedDividingWitnessArbitraryMiddleCountLossCompositionV1
import Family8Grounding.Family8NormalizedLongIntervalCoreConsumerV1

/-!
# Three-scale composition from a normalized long core

The final count-loss algebra reads only the chosen interval, stage, and
`stage_le`.  These are fields of `NormalizedLongIntervalCoreWitness`; the
discarded fine and adjacent upper barriers are not needed once the three
multiplicity estimates are supplied explicitly.
-/

open scoped ENNReal NNReal

namespace Family8NormalizedLongIntervalCoreArbitraryMiddleCountLossCompositionV1

open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8ThreeScaleFrostmanFactorAlgebraV2
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open Family8ThreeScaleFrostmanFactorCountLossV1
open Family8IdentifiedDividingWitnessCountLossCompositionV1
open Family8NormalizedLongIntervalCoreConsumerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

namespace NormalizedLongIntervalCoreWitness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma targetEpsilon : Real}

/-- Honest three-scale composition at an arbitrary positive middle radius,
using only the fields retained by the normalized long core. -/
theorem exists_stage_outerLoss_of_arbitraryMiddleCountComparison
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S)
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
    ∃ j : Nat, ∃ outerLoss : ENNReal,
      j ≤ P.N ∧
      outerLoss ≤ (delta : ENNReal) ^ (-3 * P.eta j) ∧
      D.shading.averageMultiplicity ≤
        (outerLoss * (delta : ENNReal) ^ (10 * P.eta j)) *
          frostmanMultiplicityRHS
            delta D.actualFamilyVolume (targetEpsilon / 4) gamma := by
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hmiddleScale : 0 < middleScale := htau.trans_le hTauMiddle
  have hFactors :
      sectionEightScaleCountFrostmanFactor
          delta (S.tau W.m) firstCount gamma *
        (sectionEightScaleCountFrostmanFactor
            (S.tau W.m) middleScale middleCount gamma *
          sectionEightScaleCountFrostmanFactor
            middleScale 1 thirdCount gamma) ≤
        countLoss ^ (1 - gamma / 2) *
          frostmanMultiplicityRHS
            delta D.actualFamilyVolume (targetEpsilon / 4) gamma :=
    sectionEight_threeScale_factors_le_countLoss_mul_actualRHS
      D hD htau hmiddleScale (by linarith)
        (hGammaOne.trans (by norm_num)) hcount hsmall
  refine ⟨W.stage,
    (firstLoss * thirdLoss) * countLoss ^ (1 - gamma / 2),
    W.stage_le, hAggregateLoss, ?_⟩
  exact tripleProduct_le_outerMiddleCountLossFactorization
    hTriple hFirst hMiddle hThird hFactors

#print axioms exists_stage_outerLoss_of_arbitraryMiddleCountComparison

end NormalizedLongIntervalCoreWitness

end
end Family8NormalizedLongIntervalCoreArbitraryMiddleCountLossCompositionV1
