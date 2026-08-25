import FamilyStickyGrounding.FamilyStickyScaleChainFullyAutomaticCappedInitialV2
import FamilyStickyGrounding.FamilyStickyScaleChainFullyAutomaticDeltaThresholdV2
import FamilyStickyGrounding.FamilyStickyScaleChainRelevantThetaCapRecoveredEndpointV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainFullyAutomaticRelevantEndpointV2

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
open FamilyStickyScaleChainSelectedIdentityAutomaticAllLargeProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyCapturedTubeBoxWidthV1

noncomputable section

/-!
# Fully automatic relevant Family 7 endpoint

The finite separated-factor budget forces a positive stage bound.  A single
precomputed delta threshold then gives both the capped depth-two seed and the
uniform adjacent-card endpoint bound.  The uniform automatic theta minimum
supplies the cap and every stage-window condition.  Consequently the public
endpoint accepts neither a successor nor an initial state, cap, stage window,
terminal-stage room, adjacent-card bound, or separate `delta < 1` premise.
-/

universe u

variable {delta : NNReal} {gapEpsilon targetExponent : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Numerical consequences and the canonical run -/

/-- The separated-factor budget is impossible at stage bound zero. -/
theorem stageBound_pos_of_exponentBudget
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real)) :
    1 <= N := by
  by_contra not_pos
  have N_eq : N = 0 := by omega
  subst N
  norm_num at exponent_budget

/-- The total threshold lies below the automatic theta cap, which is at most
one half once the stage window is nonempty.  Hence it also supplies the strict
upper bound on `delta` needed by the counted recursion. -/
theorem delta_lt_one_of_exponentBudget
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (delta_le : delta <=
      fullyAutomaticDeltaThreshold iota eta N gapEpsilon) :
    delta < 1 := by
  have N_pos : 1 <= N :=
    stageBound_pos_of_exponentBudget exponent_budget
  have delta_le_half : delta <= (2 : NNReal)⁻¹ := by
    calc
      delta <= fullyAutomaticDeltaThreshold iota eta N gapEpsilon := delta_le
      _ <= fullyAutomaticDeltaThetaCap iota eta N :=
        fullyAutomaticDeltaThreshold_le_cap iota eta N gapEpsilon
      _ = fullyAutomaticThetaCap iota eta N := rfl
      _ <= (2 : NNReal)⁻¹ :=
        fullyAutomaticThetaCap_le_half iota eta N_pos
  exact delta_le_half.trans_lt (by norm_num)

/-- The canonical capped stage-one state generated solely from the numerical
and geometric inputs of the fully automatic endpoint. -/
def fullyAutomaticRelevantInitialState
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <=
      fullyAutomaticDeltaThreshold iota eta N gapEpsilon) :
    RelevantThetaCappedCountedState C N gapEpsilon eta
      (fullyAutomaticThetaCap iota eta N) := by
  have N_pos : 1 <= N :=
    stageBound_pos_of_exponentBudget exponent_budget
  have delta_le_seed : delta <=
      fullyAutomaticCappedInitialDeltaThreshold
        iota eta N gapEpsilon := by
    exact delta_le.trans
      (fullyAutomaticDeltaThreshold_le_seed iota eta N gapEpsilon)
  exact
    (fullyAutomaticCappedInitialPackage C delta_pos gap_pos N_pos
      eta_monotone two_lt_eta_zero fine_refined_nonempty
      delta_le_seed).initial

/-- The terminal cap-bearing counted state of the fully automatic run. -/
def fullyAutomaticRelevantTerminalState
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <=
      fullyAutomaticDeltaThreshold iota eta N gapEpsilon) :
    RelevantThetaCappedCountedState C N gapEpsilon eta
      (fullyAutomaticThetaCap iota eta N) :=
  relevantThetaCappedCountingTerminalState C delta_pos
    (delta_lt_one_of_exponentBudget exponent_budget delta_le)
    gap_pos eta_monotone exponent_budget
    (fullyAutomaticThetaCap iota eta N)
    (fullyAutomaticThetaCapStageWindow iota eta N eta_monotone
      two_lt_eta_zero)
    (fullyAutomaticRelevantInitialState C delta_pos gap_pos eta_monotone
      two_lt_eta_zero exponent_budget fine_refined_nonempty delta_le)

/-- The terminal stage used in the recovered two-exponent profile. -/
def fullyAutomaticRelevantTerminalStage
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <=
      fullyAutomaticDeltaThreshold iota eta N gapEpsilon) : Nat :=
  (fullyAutomaticRelevantTerminalState C delta_pos gap_pos eta_monotone
    two_lt_eta_zero exponent_budget fine_refined_nonempty
    delta_le).counted.data.stage

/-! ## Fully automatic identity-cover endpoints -/

/-- The identity-cover Family 7 run yields Sticky at every scale or a literal
two-exponent Katz--Tao dividing witness.  Every recursive structural input and
every terminal-stage numerical input is generated internally. -/
theorem identityFullyAutomaticRelevant_sticky_or_recoveredWitness
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
  have delta_lt_one : delta < 1 :=
    delta_lt_one_of_exponentBudget exponent_budget delta_le
  have delta_le_uniform : delta <=
      FamilyStickyScaleChainRelevantCountedUniformThresholdEndpointV2.uniformFirstNonLargeAdjacentCardThreshold
        iota gapEpsilon eta N :=
    uniformAdjacentBound_of_le_fullyAutomaticDeltaThreshold delta_le
  simpa [fullyAutomaticRelevantTerminalStage,
      fullyAutomaticRelevantTerminalState] using
    (identityRelevantThetaCappedCounting_sticky_or_recoveredWitness_of_uniformThreshold
      fine delta_pos delta_lt_one gap_pos eta_monotone two_lt_eta_zero.le
      exponent_budget (fullyAutomaticThetaCap iota eta N)
      (fullyAutomaticThetaCapStageWindow iota eta N eta_monotone
        two_lt_eta_zero)
      (fullyAutomaticRelevantInitialState (identityRadiusCoherentCover fine)
        delta_pos gap_pos eta_monotone two_lt_eta_zero exponent_budget
        fine_refined_nonempty delta_le)
      room_at_bound delta_le_uniform)

/-- Compatibility projection of the fully automatic endpoint to the V1
literal-witness API. -/
theorem identityFullyAutomaticRelevant_sticky_or_recoveredLiteralWitness
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
      Nonempty (KatzTaoDividingWitness delta N gapEpsilon
        (recoveredProfileV2 eta
          (fullyAutomaticRelevantTerminalStage
            (identityRadiusCoherentCover fine) delta_pos gap_pos eta_monotone
            two_lt_eta_zero exponent_budget fine_refined_nonempty delta_le)
          targetExponent)) := by
  rcases identityFullyAutomaticRelevant_sticky_or_recoveredWitness fine
      delta_pos gap_pos eta_monotone two_lt_eta_zero exponent_budget
      room_at_bound fine_refined_nonempty delta_le with sticky | witness
  · exact Or.inl sticky
  · rcases witness with ⟨W⟩
    exact Or.inr ⟨W.toV1⟩

#print axioms stageBound_pos_of_exponentBudget
#print axioms delta_lt_one_of_exponentBudget
#print axioms fullyAutomaticRelevantInitialState
#print axioms fullyAutomaticRelevantTerminalState
#print axioms identityFullyAutomaticRelevant_sticky_or_recoveredWitness
#print axioms identityFullyAutomaticRelevant_sticky_or_recoveredLiteralWitness

end
end FamilyStickyScaleChainFullyAutomaticRelevantEndpointV2
