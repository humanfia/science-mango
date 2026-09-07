import Family8Grounding.Family8FirstActualCrossingThreeFactorProductV2
import Family8Grounding.Family8NormalizedLongIntervalCoreArbitraryMiddleCountLossCompositionV1

/-!
# Three-scale count-loss composition at a full-refinement first crossing

The pure Section 8 product algebra only needs the selected lower scale,
middle radius, stage, and stage bound.  A first-crossing witness carries all
of those fields.  This file composes arbitrary honest estimates for the
three visible averages into the literal stage/outer-loss conclusion about
the original datum; no analytic estimate is packaged as data.

V1 omitted the namespace of the pure product lemma and is not imported.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

open scoped ENNReal NNReal

namespace Family8FirstActualCrossingFullRefinementCountLossCompositionV2

open Family8FullRefinementActualDatumV1
open Family8IdentifiedDividingWitnessCountLossCompositionV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8ParameterLadderV1
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open Family8ThreeScaleFrostmanFactorAlgebraV2
open Family8ThreeScaleFrostmanFactorCountLossV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

namespace FirstActualNormalizedCrossingWitness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma targetEpsilon : Real}

/-- Honest three-scale composition at the literal middle radius selected by
the first-crossing witness on the full-refinement datum. -/
theorem exists_stage_outerLoss_of_threeScaleCountComparison
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
    (hGammaOne : gamma <= 1)
    (hcount :
      ((firstCount * (middleCount * thirdCount) : Nat) : ENNReal) <=
        countLoss * (Fintype.card index : ENNReal))
    (hsmall : delta <=
      sectionEightThreeScaleActualThreshold gamma
        (targetEpsilon / 4))
    {firstAverage middleAverage thirdAverage : ENNReal}
    {firstLoss thirdLoss : ENNReal}
    (hTriple : D.shading.averageMultiplicity <=
      firstAverage * (middleAverage * thirdAverage))
    (hFirst : firstAverage <= firstLoss *
      sectionEightScaleCountFrostmanFactor
        delta (S.tau W.m) firstCount gamma)
    (hMiddle : middleAverage <=
      (delta : ENNReal) ^ (10 * P.eta W.stage) *
        sectionEightScaleCountFrostmanFactor
          (S.tau W.m) W.rho middleCount gamma)
    (hThird : thirdAverage <= thirdLoss *
      sectionEightScaleCountFrostmanFactor
        W.rho 1 thirdCount gamma)
    (hAggregateLoss :
      (firstLoss * thirdLoss) * countLoss ^ (1 - gamma / 2) <=
        (delta : ENNReal) ^ (-3 * P.eta W.stage)) :
    exists j : Nat, exists outerLoss : ENNReal,
      j <= P.N /\
      outerLoss <= (delta : ENNReal) ^ (-3 * P.eta j) /\
      D.shading.averageMultiplicity <=
        (outerLoss * (delta : ENNReal) ^ (10 * P.eta j)) *
          frostmanMultiplicityRHS
            delta D.actualFamilyVolume (targetEpsilon / 4) gamma := by
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hTauMiddle : S.tau W.m <= W.rho :=
    actualDatum_tau_le_of_isBuffered
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
        S P.epsilon_pos.le W.m W.rho W.buffered
  have hmiddle : 0 < W.rho := htau.trans_le hTauMiddle
  have hFactors :
      sectionEightScaleCountFrostmanFactor
          delta (S.tau W.m) firstCount gamma *
        (sectionEightScaleCountFrostmanFactor
            (S.tau W.m) W.rho middleCount gamma *
          sectionEightScaleCountFrostmanFactor
            W.rho 1 thirdCount gamma) <=
        countLoss ^ (1 - gamma / 2) *
          frostmanMultiplicityRHS
            delta D.actualFamilyVolume (targetEpsilon / 4) gamma :=
    sectionEight_threeScale_factors_le_countLoss_mul_actualRHS
      D hD htau hmiddle (by linarith)
        (hGammaOne.trans (by norm_num)) hcount hsmall
  refine ⟨W.stage,
    (firstLoss * thirdLoss) * countLoss ^ (1 - gamma / 2),
    W.stage_le, hAggregateLoss, ?_⟩
  exact tripleProduct_le_outerMiddleCountLossFactorization
    hTriple hFirst hMiddle hThird hFactors

#print axioms exists_stage_outerLoss_of_threeScaleCountComparison

end FirstActualNormalizedCrossingWitness

end
end Family8FirstActualCrossingFullRefinementCountLossCompositionV2
