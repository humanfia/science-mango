import FamilyStickyGrounding.FamilyStickyScaleChainConcreteAutomaticNumericsV2
import FamilyStickyGrounding.FamilyStickyScaleChainFullyAutomaticFinalOutcomeV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainConcreteAutomaticFinalOutcomeV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainTwoExponentStoppingCoreV2
open FamilyStickyScaleChainTwoParameterRecoveredEndpointV2
open FamilyStickyScaleChainFullyAutomaticRelevantEndpointV2
open FamilyStickyScaleChainFullyAutomaticFinalOutcomeV2
open FamilyStickyScaleChainConcreteAutomaticNumericsV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyCapturedTubeBoxWidthV1

noncomputable section

/-!
# Concrete certificate-preserving automatic Family 7 outcome

Specialize the fully automatic certificate-preserving dichotomy to five
stages, gap exponent one half, constant profile three, and target exponent
four.  The public API retains only the fine family, positivity and
nonemptiness geometry, and comparison with the single concrete delta
threshold.
-/

universe u

variable {delta : NNReal}
  {iota : Type u} [Fintype iota] [DecidableEq iota]

/-! ## Concrete terminal state -/

/-- The cap-bearing terminal state of the fixed concrete automatic run. -/
def concreteAutomaticFinalTerminalState
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <= concreteAutomaticDeltaThreshold iota) :=
  fullyAutomaticRelevantTerminalState (identityRadiusCoherentCover fine)
    delta_pos concreteAutomaticGap_pos concreteAutomaticEta_monotone
    concreteAutomaticEta_zero_gt_two concreteAutomaticExponentBudget
    fine_refined_nonempty delta_le

/-! ## Certificate-preserving concrete dichotomy -/

/-- For the fixed feasible numerical choice, the all-large branch retains
the literal certificate on the concrete automatic terminal scale chain and
pairs it with identity Sticky; the other branch is the recovered
two-exponent witness. -/
theorem identityConcreteAutomaticFinal_allLargeAndSticky_or_recoveredWitness
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <= concreteAutomaticDeltaThreshold iota) :
    ((concreteAutomaticFinalTerminalState fine delta_pos
          fine_refined_nonempty delta_le).counted.data.scales.AllStepsLarge
        concreteAutomaticGap /\
      (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal))) \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta
        concreteAutomaticStageBound concreteAutomaticGap
        concreteAutomaticTargetExponent
        (recoveredProfileV2 concreteAutomaticEta
          (concreteAutomaticTerminalStage fine delta_pos
            fine_refined_nonempty delta_le)
          concreteAutomaticTargetExponent)) := by
  simpa [concreteAutomaticFinalTerminalState,
      concreteAutomaticTerminalStage, concreteAutomaticDeltaThreshold] using
    (identityFullyAutomaticFinal_allLargeAndSticky_or_recoveredWitness
      (N := concreteAutomaticStageBound) (eta := concreteAutomaticEta)
      (targetExponent := concreteAutomaticTargetExponent)
      fine delta_pos concreteAutomaticGap_pos concreteAutomaticEta_monotone
      concreteAutomaticEta_zero_gt_two concreteAutomaticExponentBudget
      concreteAutomaticRoomAtBound fine_refined_nonempty delta_le)

/-! ## Standard projections -/

/-- Discard the concrete terminal all-large certificate while retaining the
two-exponent witness API. -/
theorem identityConcreteAutomaticFinal_sticky_or_recoveredWitness
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <= concreteAutomaticDeltaThreshold iota) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal)) \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta
        concreteAutomaticStageBound concreteAutomaticGap
        concreteAutomaticTargetExponent
        (recoveredProfileV2 concreteAutomaticEta
          (concreteAutomaticTerminalStage fine delta_pos
            fine_refined_nonempty delta_le)
          concreteAutomaticTargetExponent)) := by
  rcases
      identityConcreteAutomaticFinal_allLargeAndSticky_or_recoveredWitness
        fine delta_pos fine_refined_nonempty delta_le with
    ⟨_hall, sticky⟩ | witness
  · exact Or.inl sticky
  · exact Or.inr witness

/-- Compatibility projection of the concrete certificate-preserving outcome
to the V1 literal Katz--Tao dividing-witness API. -/
theorem identityConcreteAutomaticFinal_sticky_or_recoveredLiteralWitness
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <= concreteAutomaticDeltaThreshold iota) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal)) \/
      Nonempty (KatzTaoDividingWitness delta concreteAutomaticStageBound
        concreteAutomaticGap
        (recoveredProfileV2 concreteAutomaticEta
          (concreteAutomaticTerminalStage fine delta_pos
            fine_refined_nonempty delta_le)
          concreteAutomaticTargetExponent)) := by
  rcases identityConcreteAutomaticFinal_sticky_or_recoveredWitness fine
      delta_pos fine_refined_nonempty delta_le with sticky | witness
  · exact Or.inl sticky
  · rcases witness with ⟨W⟩
    exact Or.inr ⟨W.toV1⟩

#print axioms concreteAutomaticFinalTerminalState
#print axioms identityConcreteAutomaticFinal_allLargeAndSticky_or_recoveredWitness
#print axioms identityConcreteAutomaticFinal_sticky_or_recoveredWitness
#print axioms identityConcreteAutomaticFinal_sticky_or_recoveredLiteralWitness

end
end FamilyStickyScaleChainConcreteAutomaticFinalOutcomeV2
