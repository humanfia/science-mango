import FamilyStickyGrounding.FamilyStickyScaleChainRelevantThetaCapCountedDriverV2
import FamilyStickyGrounding.FamilyStickyScaleChainRelevantCountedRecoveredEndpointV2
import FamilyStickyGrounding.FamilyStickyScaleChainRelevantCountedUniformThresholdEndpointV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainRelevantThetaCapRecoveredEndpointV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainFirstNonLargeAdjacentCardBudgetProducerV1
open FamilyStickyScaleChainTwoExponentStoppingCoreV2
open FamilyStickyScaleChainTwoParameterRecoveredEndpointV2
open FamilyStickyScaleChainTwoParameterTerminalNoSplitV2
open FamilyStickyScaleChainRelevantIntervalEnvelopeInvariantV2
open FamilyStickyScaleChainRelevantThetaCapCountedDriverV2
open FamilyStickyScaleChainRelevantCountedRecoveredEndpointV2
open FamilyStickyScaleChainRelevantCountedUniformThresholdEndpointV2
open FamilyStickyScaleChainSelectedIdentityAutomaticAllLargeProducerV1
open FamilyStickyScaleChainSelectedIdentityDirectNormalizerProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyCapturedTubeBoxWidthV1

noncomputable section

/-!
# Recovered endpoint from cap-bearing relevant counted stopping

The cap-bearing counted recursion constructs its successor internally and
retains both terminal facts consumed by the recovered endpoint: literal
terminal no-split and the global-product estimate at the first non-large
interval.  Thus no successor, terminal no-split, or global-product premise is
accepted by the results below.
-/

universe u

variable {delta : NNReal} {gapEpsilon targetExponent : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Terminal-stage numerical inputs -/

/-- The automatic cap-bearing recursion closes the complete non-large branch.
Its two analytic terminal premises are obtained directly from the terminal
state rather than re-assumed. -/
theorem relevantThetaCappedCounting_allLarge_or_recoveredWitness
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal)
    (stageWindow : RelevantThetaCapStageWindow N eta iota cap)
    (initial : RelevantThetaCappedCountedState C N gapEpsilon eta cap)
    (strict_room : eta
        (relevantThetaCappedCountingTerminalState C delta_pos delta_lt_one
          gap_pos eta_monotone exponent_budget cap stageWindow initial).counted.data.stage <
      targetExponent)
    (delta_le : delta <= firstNonLargeAdjacentCardThreshold iota gapEpsilon
      (eta
        ((relevantThetaCappedCountingTerminalState C delta_pos delta_lt_one
          gap_pos eta_monotone exponent_budget cap stageWindow initial).counted.data.stage - 1))) :
    (relevantThetaCappedCountingTerminalState C delta_pos delta_lt_one
        gap_pos eta_monotone exponent_budget cap stageWindow initial).counted.data.scales.AllStepsLarge
          gapEpsilon \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
        targetExponent
        (recoveredProfileV2 eta
          (relevantThetaCappedCountingTerminalState C delta_pos delta_lt_one
            gap_pos eta_monotone exponent_budget cap stageWindow initial).counted.data.stage
          targetExponent)) := by
  let terminal := relevantThetaCappedCountingTerminalState C delta_pos
    delta_lt_one gap_pos eta_monotone exponent_budget cap stageWindow initial
  by_cases hall : terminal.counted.data.scales.AllStepsLarge gapEpsilon
  · exact Or.inl hall
  · refine Or.inr
      (exists_twoExponentRecoveredLiteralWitnessV2_of_globalProduct_and_terminalNoSplit
        C (terminal.counted.data.buffered C delta_pos)
        terminal.counted.data.stage terminal.counted.data.stage_pos
        terminal.counted.data.stage_le eta_monotone two_le_zero ?_ hall ?_ ?_
        gap_pos delta_pos ?_)
    · simpa [terminal] using strict_room
    · exact
        relevantThetaCappedCountingTerminalState_actualGlobalProductAt_firstNonLarge_le
          C delta_pos delta_lt_one gap_pos eta_monotone exponent_budget cap
            stageWindow initial hall
    · exact relevantThetaCappedCountingTerminalState_terminalNoSplit C
        delta_pos delta_lt_one gap_pos eta_monotone exponent_budget cap
          stageWindow initial hall
    · simpa [terminal] using delta_le

/-- Identity-cover specialization: the all-large branch is the automatic
Sticky conclusion and the other branch is the recovered two-exponent
witness. -/
theorem identityRelevantThetaCappedCounting_sticky_or_recoveredWitness
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal)
    (stageWindow : RelevantThetaCapStageWindow N eta iota cap)
    (initial : RelevantThetaCappedCountedState
      (identityRadiusCoherentCover fine) N gapEpsilon eta cap)
    (strict_room : eta
        (relevantThetaCappedCountingTerminalState
          (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
          eta_monotone exponent_budget cap stageWindow initial).counted.data.stage <
      targetExponent)
    (delta_le : delta <= firstNonLargeAdjacentCardThreshold iota gapEpsilon
      (eta
        ((relevantThetaCappedCountingTerminalState
          (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
          eta_monotone exponent_budget cap stageWindow initial).counted.data.stage - 1))) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal)) \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
        targetExponent
        (recoveredProfileV2 eta
          (relevantThetaCappedCountingTerminalState
            (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
            eta_monotone exponent_budget cap stageWindow initial).counted.data.stage
          targetExponent)) := by
  let terminal := relevantThetaCappedCountingTerminalState
    (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
      eta_monotone exponent_budget cap stageWindow initial
  rcases relevantThetaCappedCounting_allLarge_or_recoveredWitness
      (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
      eta_monotone two_le_zero exponent_budget cap stageWindow initial
      strict_room delta_le with hall | witness
  · exact Or.inl
      (identityIsStickyAtEveryScale_of_allStepsLarge fine
        terminal.counted.data.scales terminal.counted.data.depth_pos delta_pos
        hall)
  · exact Or.inr witness

/-- Compatibility projection of the cap-bearing identity endpoint to the V1
literal-witness API. -/
theorem identityRelevantThetaCappedCounting_sticky_or_recoveredLiteralWitness
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal)
    (stageWindow : RelevantThetaCapStageWindow N eta iota cap)
    (initial : RelevantThetaCappedCountedState
      (identityRadiusCoherentCover fine) N gapEpsilon eta cap)
    (strict_room : eta
        (relevantThetaCappedCountingTerminalState
          (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
          eta_monotone exponent_budget cap stageWindow initial).counted.data.stage <
      targetExponent)
    (delta_le : delta <= firstNonLargeAdjacentCardThreshold iota gapEpsilon
      (eta
        ((relevantThetaCappedCountingTerminalState
          (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
          eta_monotone exponent_budget cap stageWindow initial).counted.data.stage - 1))) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal)) \/
      Nonempty (KatzTaoDividingWitness delta N gapEpsilon
        (recoveredProfileV2 eta
          (relevantThetaCappedCountingTerminalState
            (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
            eta_monotone exponent_budget cap stageWindow initial).counted.data.stage
          targetExponent)) := by
  rcases identityRelevantThetaCappedCounting_sticky_or_recoveredWitness
      fine delta_pos delta_lt_one gap_pos eta_monotone two_le_zero
      exponent_budget cap stageWindow initial strict_room delta_le with
    sticky | witness
  · exact Or.inl sticky
  · rcases witness with ⟨W⟩
    exact Or.inr ⟨W.toV1⟩

/-! ## Precomputed finite-stage numerical inputs -/

/-- The generic cap-bearing endpoint with terminal-stage numerical inputs
replaced by the fixed bound-stage room and finite adjacent-card minimum. -/
theorem relevantThetaCappedCounting_allLarge_or_recoveredWitness_of_uniformThreshold
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal)
    (stageWindow : RelevantThetaCapStageWindow N eta iota cap)
    (initial : RelevantThetaCappedCountedState C N gapEpsilon eta cap)
    (room_at_bound : eta N < targetExponent)
    (delta_le_uniform : delta <=
      uniformFirstNonLargeAdjacentCardThreshold iota gapEpsilon eta N) :
    (relevantThetaCappedCountingTerminalState C delta_pos delta_lt_one
        gap_pos eta_monotone exponent_budget cap stageWindow initial).counted.data.scales.AllStepsLarge
          gapEpsilon \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
        targetExponent
        (recoveredProfileV2 eta
          (relevantThetaCappedCountingTerminalState C delta_pos delta_lt_one
            gap_pos eta_monotone exponent_budget cap stageWindow initial).counted.data.stage
          targetExponent)) := by
  let terminal := relevantThetaCappedCountingTerminalState C delta_pos
    delta_lt_one gap_pos eta_monotone exponent_budget cap stageWindow initial
  have terminal_room : eta terminal.counted.data.stage < targetExponent :=
    (eta_monotone terminal.counted.data.stage_le).trans_lt room_at_bound
  have terminal_delta : delta <=
      firstNonLargeAdjacentCardThreshold iota gapEpsilon
        (eta (terminal.counted.data.stage - 1)) :=
    delta_le_uniform.trans
      (uniformFirstNonLargeAdjacentCardThreshold_le_stage iota gapEpsilon eta N
        terminal.counted.data.stage terminal.counted.data.stage_pos
        terminal.counted.data.stage_le)
  exact relevantThetaCappedCounting_allLarge_or_recoveredWitness C delta_pos
    delta_lt_one gap_pos eta_monotone two_le_zero exponent_budget cap
      stageWindow initial terminal_room terminal_delta

/-- Identity-cover cap-bearing endpoint with all numerical endpoint inputs
fixed before the recursion starts. -/
theorem identityRelevantThetaCappedCounting_sticky_or_recoveredWitness_of_uniformThreshold
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal)
    (stageWindow : RelevantThetaCapStageWindow N eta iota cap)
    (initial : RelevantThetaCappedCountedState
      (identityRadiusCoherentCover fine) N gapEpsilon eta cap)
    (room_at_bound : eta N < targetExponent)
    (delta_le_uniform : delta <=
      uniformFirstNonLargeAdjacentCardThreshold iota gapEpsilon eta N) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal)) \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
        targetExponent
        (recoveredProfileV2 eta
          (relevantThetaCappedCountingTerminalState
            (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
            eta_monotone exponent_budget cap stageWindow initial).counted.data.stage
          targetExponent)) := by
  let terminal := relevantThetaCappedCountingTerminalState
    (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
      eta_monotone exponent_budget cap stageWindow initial
  have terminal_room : eta terminal.counted.data.stage < targetExponent :=
    (eta_monotone terminal.counted.data.stage_le).trans_lt room_at_bound
  have terminal_delta : delta <=
      firstNonLargeAdjacentCardThreshold iota gapEpsilon
        (eta (terminal.counted.data.stage - 1)) :=
    delta_le_uniform.trans
      (uniformFirstNonLargeAdjacentCardThreshold_le_stage iota gapEpsilon eta N
        terminal.counted.data.stage terminal.counted.data.stage_pos
        terminal.counted.data.stage_le)
  exact identityRelevantThetaCappedCounting_sticky_or_recoveredWitness fine
    delta_pos delta_lt_one gap_pos eta_monotone two_le_zero exponent_budget cap
      stageWindow initial terminal_room terminal_delta

/-- V1 literal-witness projection of the uniform cap-bearing identity
endpoint. -/
theorem identityRelevantThetaCappedCounting_sticky_or_recoveredLiteralWitness_of_uniformThreshold
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal)
    (stageWindow : RelevantThetaCapStageWindow N eta iota cap)
    (initial : RelevantThetaCappedCountedState
      (identityRadiusCoherentCover fine) N gapEpsilon eta cap)
    (room_at_bound : eta N < targetExponent)
    (delta_le_uniform : delta <=
      uniformFirstNonLargeAdjacentCardThreshold iota gapEpsilon eta N) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal)) \/
      Nonempty (KatzTaoDividingWitness delta N gapEpsilon
        (recoveredProfileV2 eta
          (relevantThetaCappedCountingTerminalState
            (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
            eta_monotone exponent_budget cap stageWindow initial).counted.data.stage
          targetExponent)) := by
  rcases
      identityRelevantThetaCappedCounting_sticky_or_recoveredWitness_of_uniformThreshold
        fine delta_pos delta_lt_one gap_pos eta_monotone two_le_zero
        exponent_budget cap stageWindow initial room_at_bound delta_le_uniform with
    sticky | witness
  · exact Or.inl sticky
  · rcases witness with ⟨W⟩
    exact Or.inr ⟨W.toV1⟩

#print axioms relevantThetaCappedCounting_allLarge_or_recoveredWitness
#print axioms identityRelevantThetaCappedCounting_sticky_or_recoveredWitness
#print axioms identityRelevantThetaCappedCounting_sticky_or_recoveredLiteralWitness
#print axioms relevantThetaCappedCounting_allLarge_or_recoveredWitness_of_uniformThreshold
#print axioms identityRelevantThetaCappedCounting_sticky_or_recoveredWitness_of_uniformThreshold
#print axioms identityRelevantThetaCappedCounting_sticky_or_recoveredLiteralWitness_of_uniformThreshold

end
end FamilyStickyScaleChainRelevantThetaCapRecoveredEndpointV2
