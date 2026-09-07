import Family8Grounding.Family8IdentifiedDividingWitnessOuterMiddleCompositionV2
import Family8Grounding.Family8ThreeScaleActualFrostmanFactorAbsorptionV2

open scoped ENNReal NNReal

namespace Family8IdentifiedDividingWitnessScaleCountCompositionV1

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

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Identified-witness composition with official scale-count factors

The three scale-count factors no longer need to be recombined by the
geometric producer.  Exact uniform count multiplication and the explicit
small-scale threshold automatically turn their product into the actual
source Frostman right-hand side.

Thus the theorem below consumes only the literal triple decomposition and
the three genuine multiplicity estimates.  It does not assume the final
factorized endpoint.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma targetEpsilon : Real}

/-- Exact scale-count specialization of the outer-middle-outer composition.
The source-volume normalization and all factor algebra are discharged
automatically. -/
theorem exists_stage_outerLoss_of_threeScaleCountEstimates
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family C P.N P.epsilon P.eta S)
    {firstCount middleCount thirdCount : Nat}
    (hTargetEpsilon : 0 < targetEpsilon)
    (hGammaOne : gamma <= 1)
    (hcount : Fintype.card index =
      firstCount * (middleCount * thirdCount))
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
    (hFirstLoss : firstLoss <=
      (delta : ENNReal) ^ (-2 * P.eta W.stage))
    (hMiddle : middleAverage <=
      (delta : ENNReal) ^ (10 * P.eta W.stage) *
        sectionEightScaleCountFrostmanFactor
          (S.tau W.m) (S.theta W.m) middleCount gamma)
    (hThird : thirdAverage <= thirdLoss *
      sectionEightScaleCountFrostmanFactor
        (S.theta W.m) 1 thirdCount gamma)
    (hThirdLoss : thirdLoss <=
      (delta : ENNReal) ^ (-P.eta W.stage)) :
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
        frostmanMultiplicityRHS
          delta D.actualFamilyVolume (targetEpsilon / 4) gamma :=
    sectionEight_threeScale_factors_le_actualRHS
      D hD htau htheta (by linarith) (hGammaOne.trans (by norm_num))
      hcount hsmall
  exact
    Family8IdentifiedDividingWitnessOuterMiddleCompositionV2.Witness.exists_stage_outerLoss_outerMiddleFactorization
      D C S P W hD.delta_pos hTriple hFirst hFirstLoss
        hMiddle hThird hThirdLoss hFactors

#print axioms exists_stage_outerLoss_of_threeScaleCountEstimates

end Witness

end

end Family8IdentifiedDividingWitnessScaleCountCompositionV1
