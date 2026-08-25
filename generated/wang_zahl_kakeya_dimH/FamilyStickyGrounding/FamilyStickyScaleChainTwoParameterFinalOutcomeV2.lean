import FamilyStickyGrounding.FamilyStickyScaleChainTwoParameterRecoveredEndpointV2
import FamilyStickyGrounding.FamilyStickyScaleChainSelectedIdentityAutomaticAllLargeProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainTwoParameterFinalOutcomeV2

open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainRootedRefinementTreeV1
open FamilyStickyScaleChainConstantBearingStoppingEndpointV1
open FamilyStickyScaleChainActualStoppingUpstreamClosureV1
open FamilyStickyScaleChainDividingFiniteNodeProducerV1
open FamilyStickyScaleChainFirstNonLargeRelevantNodeProducerV1
open FamilyStickyScaleChainSelectedGlobalExponentProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyScaleChainSelectedIdentityDirectNormalizerProducerV1
open FamilyStickyCapturedTubeBoxWidthV1
open FamilyStickyScaleChainTwoParameterRecoveredEndpointV2
open FamilyStickyScaleChainSelectedIdentityAutomaticAllLargeProducerV1

noncomputable section

/-!
# Two-parameter final identity outcome

The geometric scale gap and the target exponent remain independent in the
top-level stopping dichotomy.  If every interval is large for `gapEpsilon`,
the identity cover is sticky with the explicit finite constants already
proved for that branch.  Otherwise, the selected global estimates and the
relevant-node checks at the computed first non-large interval give the V1
literal dividing witness with `recoveredProfileV2`.
-/

universe u

variable {delta : NNReal} {gapEpsilon targetExponent : Real}
  {depth chainDepth N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]

/-- The honest final dichotomy retains the all-large certificate in its left
branch and returns the existing V1 literal witness in its right branch. -/
theorem identityTwoParameterFinalOutcomeV2
    (fine : UniformTubeFamily delta iota)
    (T : FiniteScaleSequence delta depth)
    (hdepth : 0 < depth)
    (R : IntervalRootedRefinementScaleTree T)
    (B : BufferedChainFamily depth chainDepth)
    (slot : Fin N)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < targetExponent)
    (gap_pos : 0 < gapEpsilon)
    (delta_pos : 0 < delta)
    (delta_le : delta <= selectedGlobalAdjacentRecoveredThresholdV2
      eta (oneBasedStage slot) gapEpsilon targetExponent iota)
    (globalEstimates : forall hnot : Not (T.AllStepsLarge gapEpsilon),
      SelectedGlobalExponentEstimates B T
        (selectedProfileV2 eta (oneBasedStage slot) targetExponent)
        (oneBasedStage slot)
        (firstNonLargeStep T gapEpsilon hnot))
    (relevantNodeBounds : forall hnot : Not (T.AllStepsLarge gapEpsilon),
      VerifiedRelevantStepNodeLowerBounds
        (epsilon := gapEpsilon)
        (profile := selectedProfileV2 eta (oneBasedStage slot) targetExponent)
        (stage := oneBasedStage slot)
        ((identityRadiusCoherentCover fine).toActualIntervalCovers T) R
        (firstNonLargeStep T gapEpsilon hnot)) :
    (T.AllStepsLarge gapEpsilon ∧
        (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
          ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
          (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
            (Fintype.card iota : ENNReal))) ∨
      Nonempty (KatzTaoDividingWitness delta N gapEpsilon
        (recoveredProfileV2 eta (oneBasedStage slot) targetExponent)) := by
  by_cases hall : T.AllStepsLarge gapEpsilon
  · exact Or.inl ⟨hall,
      identityIsStickyAtEveryScale_of_allStepsLarge
        fine T hdepth delta_pos hall⟩
  · exact Or.inr
      (exists_recoveredLiteralWitnessV2_of_selectedGlobalEstimates
        (identityRadiusCoherentCover fine) R B
        (oneBasedStage slot) (oneBasedStage_pos slot) (oneBasedStage_le slot)
        eta_monotone two_le_zero strict_room hall
        (globalEstimates hall) (relevantNodeBounds hall)
        gap_pos delta_pos delta_le)

/-- Projection of the certificate-bearing dichotomy to the usual mathematical
statement: the identity cover is sticky, or a literal dividing witness is
recovered at the independent gap parameter. -/
theorem identitySticky_or_recoveredLiteralWitnessV2
    (fine : UniformTubeFamily delta iota)
    (T : FiniteScaleSequence delta depth)
    (hdepth : 0 < depth)
    (R : IntervalRootedRefinementScaleTree T)
    (B : BufferedChainFamily depth chainDepth)
    (slot : Fin N)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < targetExponent)
    (gap_pos : 0 < gapEpsilon)
    (delta_pos : 0 < delta)
    (delta_le : delta <= selectedGlobalAdjacentRecoveredThresholdV2
      eta (oneBasedStage slot) gapEpsilon targetExponent iota)
    (globalEstimates : forall hnot : Not (T.AllStepsLarge gapEpsilon),
      SelectedGlobalExponentEstimates B T
        (selectedProfileV2 eta (oneBasedStage slot) targetExponent)
        (oneBasedStage slot)
        (firstNonLargeStep T gapEpsilon hnot))
    (relevantNodeBounds : forall hnot : Not (T.AllStepsLarge gapEpsilon),
      VerifiedRelevantStepNodeLowerBounds
        (epsilon := gapEpsilon)
        (profile := selectedProfileV2 eta (oneBasedStage slot) targetExponent)
        (stage := oneBasedStage slot)
        ((identityRadiusCoherentCover fine).toActualIntervalCovers T) R
        (firstNonLargeStep T gapEpsilon hnot)) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal)) ∨
      Nonempty (KatzTaoDividingWitness delta N gapEpsilon
        (recoveredProfileV2 eta (oneBasedStage slot) targetExponent)) := by
  rcases identityTwoParameterFinalOutcomeV2
      fine T hdepth R B slot eta_monotone two_le_zero strict_room
      gap_pos delta_pos delta_le globalEstimates relevantNodeBounds with
    allLarge | recovered
  · exact Or.inl allLarge.2
  · exact Or.inr recovered

#print axioms identityTwoParameterFinalOutcomeV2
#print axioms identitySticky_or_recoveredLiteralWitnessV2

end
end FamilyStickyScaleChainTwoParameterFinalOutcomeV2
