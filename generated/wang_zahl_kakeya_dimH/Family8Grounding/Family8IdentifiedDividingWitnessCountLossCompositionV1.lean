import Family8Grounding.Family8IdentifiedDividingWitnessOuterMiddleCompositionV2
import Family8Grounding.Family8ThreeScaleFrostmanFactorCountLossV1
import Mathlib.Tactic

open scoped ENNReal NNReal

namespace Family8IdentifiedDividingWitnessCountLossCompositionV1

open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8ThreeScaleFrostmanFactorAlgebraV2
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open Family8ThreeScaleFrostmanFactorCountLossV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Identified-witness composition with honest uniform-count loss

This successor removes the exact cardinality product required by the V1
scale-count composition.  The genuine one-sided count comparison contributes
`countLoss ^ (1 - gamma / 2)` to the same outside-loss budget as the first
and third analytic estimates.  No conclusion-valued premise is introduced:
the producer supplies the three separate multiplicity estimates and one
scalar aggregate loss cap.
-/

/-- Pure scalar composition with the uniform-count loss kept visible. -/
theorem tripleProduct_le_outerMiddleCountLossFactorization
    {delta : NNReal} {eta gamma : Real}
    {source firstAverage middleAverage thirdAverage : ENNReal}
    {firstLoss thirdLoss countLoss : ENNReal}
    {firstFactor middleFactor thirdFactor sourceRHS : ENNReal}
    (hTriple :
      source <= firstAverage * (middleAverage * thirdAverage))
    (hFirst : firstAverage <= firstLoss * firstFactor)
    (hMiddle : middleAverage <=
      (delta : ENNReal) ^ (10 * eta) * middleFactor)
    (hThird : thirdAverage <= thirdLoss * thirdFactor)
    (hFactors :
      firstFactor * (middleFactor * thirdFactor) <=
        countLoss ^ (1 - gamma / 2) * sourceRHS) :
    source <=
      (((firstLoss * thirdLoss) * countLoss ^ (1 - gamma / 2)) *
          (delta : ENNReal) ^ (10 * eta)) * sourceRHS := by
  calc
    source <= firstAverage * (middleAverage * thirdAverage) := hTriple
    _ <= (firstLoss * firstFactor) *
        (((delta : ENNReal) ^ (10 * eta) * middleFactor) *
          (thirdLoss * thirdFactor)) :=
      mul_le_mul' hFirst (mul_le_mul' hMiddle hThird)
    _ = ((firstLoss * thirdLoss) *
          (delta : ENNReal) ^ (10 * eta)) *
        (firstFactor * (middleFactor * thirdFactor)) := by
      ac_rfl
    _ <= ((firstLoss * thirdLoss) *
          (delta : ENNReal) ^ (10 * eta)) *
        (countLoss ^ (1 - gamma / 2) * sourceRHS) :=
      mul_le_mul' le_rfl hFactors
    _ = (((firstLoss * thirdLoss) *
            countLoss ^ (1 - gamma / 2)) *
          (delta : ENNReal) ^ (10 * eta)) * sourceRHS := by
      ac_rfl

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma targetEpsilon : Real}

/-- Honest uniform-count specialization of the identified long-interval
composition.  The exact count equality and the source-volume normalization
are discharged automatically.  The sole scalar budget left to the producer
is the aggregate of its two outside losses and the forced count loss. -/
theorem exists_stage_outerLoss_of_threeScaleCountComparison
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family C P.N P.epsilon P.eta S)
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
          (S.tau W.m) (S.theta W.m) middleCount gamma)
    (hThird : thirdAverage <= thirdLoss *
      sectionEightScaleCountFrostmanFactor
        (S.theta W.m) 1 thirdCount gamma)
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
  have htheta : 0 < S.theta W.m :=
    htau.trans_le (S.tau_le_theta W.m)
  have hFactors :
      sectionEightScaleCountFrostmanFactor
          delta (S.tau W.m) firstCount gamma *
        (sectionEightScaleCountFrostmanFactor
            (S.tau W.m) (S.theta W.m) middleCount gamma *
          sectionEightScaleCountFrostmanFactor
            (S.theta W.m) 1 thirdCount gamma) <=
        countLoss ^ (1 - gamma / 2) *
          frostmanMultiplicityRHS
            delta D.actualFamilyVolume (targetEpsilon / 4) gamma :=
    sectionEight_threeScale_factors_le_countLoss_mul_actualRHS
      D hD htau htheta (by linarith) (hGammaOne.trans (by norm_num))
        hcount hsmall
  refine ⟨W.stage,
    (firstLoss * thirdLoss) * countLoss ^ (1 - gamma / 2),
    W.stage_le, hAggregateLoss, ?_⟩
  exact tripleProduct_le_outerMiddleCountLossFactorization
    hTriple hFirst hMiddle hThird hFactors

#print axioms exists_stage_outerLoss_of_threeScaleCountComparison

end Witness

#print axioms tripleProduct_le_outerMiddleCountLossFactorization

end

end Family8IdentifiedDividingWitnessCountLossCompositionV1
