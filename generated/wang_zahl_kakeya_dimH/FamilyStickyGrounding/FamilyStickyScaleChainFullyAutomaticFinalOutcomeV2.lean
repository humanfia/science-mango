import FamilyStickyGrounding.FamilyStickyScaleChainFullyAutomaticRelevantEndpointV2
import FamilyStickyGrounding.FamilyStickyScaleChainRelevantThetaCapRecoveredEndpointV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainFullyAutomaticFinalOutcomeV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainTwoExponentStoppingCoreV2
open FamilyStickyScaleChainTwoParameterRecoveredEndpointV2
open FamilyStickyScaleChainRelevantThetaCapCountedDriverV2
open FamilyStickyScaleChainRelevantThetaCapRecoveredEndpointV2
open FamilyStickyScaleChainFullyAutomaticCappedInitialV2
open FamilyStickyScaleChainFullyAutomaticDeltaThresholdV2
open FamilyStickyScaleChainFullyAutomaticRelevantEndpointV2
open FamilyStickyScaleChainSelectedIdentityAutomaticAllLargeProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyCapturedTubeBoxWidthV1

noncomputable section

/-!
# Certificate-preserving fully automatic Family 7 outcome

The usual fully automatic endpoint projects the all-large branch directly to
Sticky.  Here the stronger outcome retains the literal `AllStepsLarge`
certificate of the automatically generated terminal scale chain and pairs it
with that Sticky conclusion.  The recovered branch is unchanged.

No recursive object or terminal-stage numerical datum is exposed by the
public interface.
-/

universe u

variable {delta : NNReal} {gapEpsilon targetExponent : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]

/-! ## Certificate-preserving dichotomy -/

/-- The fully automatic identity-cover run either retains its literal
terminal all-large certificate together with the induced Sticky conclusion,
or produces the recovered two-exponent Katz--Tao dividing witness.

The cap, stage window, initial state, strict `delta < 1` bound, and terminal
stage inputs are all constructed internally. -/
theorem identityFullyAutomaticFinal_allLargeAndSticky_or_recoveredWitness
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <=
      fullyAutomaticDeltaThreshold iota eta N gapEpsilon) :
    ((fullyAutomaticRelevantTerminalState
          (identityRadiusCoherentCover fine) delta_pos gap_pos eta_monotone
          two_lt_eta_zero exponent_budget fine_refined_nonempty
          delta_le).counted.data.scales.AllStepsLarge gapEpsilon /\
      (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal))) \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
        targetExponent
        (recoveredProfileV2 eta
          (fullyAutomaticRelevantTerminalStage
            (identityRadiusCoherentCover fine) delta_pos gap_pos eta_monotone
            two_lt_eta_zero exponent_budget fine_refined_nonempty delta_le)
          targetExponent)) := by
  have delta_lt_one : delta < 1 :=
    delta_lt_one_of_exponentBudget exponent_budget delta_le
  have delta_le_uniform : delta <=
      FamilyStickyScaleChainRelevantCountedUniformThresholdEndpointV2.uniformFirstNonLargeAdjacentCardThreshold
        iota gapEpsilon eta N :=
    uniformAdjacentBound_of_le_fullyAutomaticDeltaThreshold delta_le
  have run :=
    relevantThetaCappedCounting_allLarge_or_recoveredWitness_of_uniformThreshold
      (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
      eta_monotone two_lt_eta_zero.le exponent_budget
      (fullyAutomaticThetaCap iota eta N)
      (fullyAutomaticThetaCapStageWindow iota eta N eta_monotone
        two_lt_eta_zero)
      (fullyAutomaticRelevantInitialState (identityRadiusCoherentCover fine)
        delta_pos gap_pos eta_monotone two_lt_eta_zero exponent_budget
        fine_refined_nonempty delta_le)
      room_at_bound delta_le_uniform
  rcases run with hall | witness
  · refine Or.inl <| ⟨?_, ?_⟩
    · simpa [fullyAutomaticRelevantTerminalState] using hall
    · let terminal := fullyAutomaticRelevantTerminalState
          (identityRadiusCoherentCover fine) delta_pos gap_pos eta_monotone
          two_lt_eta_zero exponent_budget fine_refined_nonempty delta_le
      exact identityIsStickyAtEveryScale_of_allStepsLarge fine
        terminal.counted.data.scales terminal.counted.data.depth_pos delta_pos
        (by simpa [terminal, fullyAutomaticRelevantTerminalState] using hall)
  · exact Or.inr <| by
      simpa [fullyAutomaticRelevantTerminalStage,
        fullyAutomaticRelevantTerminalState] using witness

/-! ## Standard projection -/

/-- Discarding the retained terminal certificate recovers the usual fully
automatic Sticky-or-two-exponent-witness endpoint. -/
theorem identityFullyAutomaticFinal_sticky_or_recoveredWitness
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <=
      fullyAutomaticDeltaThreshold iota eta N gapEpsilon) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal)) \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
        targetExponent
        (recoveredProfileV2 eta
          (fullyAutomaticRelevantTerminalStage
            (identityRadiusCoherentCover fine) delta_pos gap_pos eta_monotone
            two_lt_eta_zero exponent_budget fine_refined_nonempty delta_le)
          targetExponent)) := by
  rcases identityFullyAutomaticFinal_allLargeAndSticky_or_recoveredWitness
      fine delta_pos gap_pos eta_monotone two_lt_eta_zero exponent_budget
      room_at_bound fine_refined_nonempty delta_le with
    ⟨_hall, sticky⟩ | witness
  · exact Or.inl sticky
  · exact Or.inr witness

#print axioms identityFullyAutomaticFinal_allLargeAndSticky_or_recoveredWitness
#print axioms identityFullyAutomaticFinal_sticky_or_recoveredWitness

end
end FamilyStickyScaleChainFullyAutomaticFinalOutcomeV2
