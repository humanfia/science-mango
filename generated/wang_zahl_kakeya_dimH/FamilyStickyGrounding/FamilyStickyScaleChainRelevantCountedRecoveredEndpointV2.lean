import FamilyStickyGrounding.FamilyStickyScaleChainRelevantCountedStoppingDriverV2
import FamilyStickyGrounding.FamilyStickyScaleChainSelectedIdentityAutomaticAllLargeProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainRelevantCountedRecoveredEndpointV2

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
open FamilyStickyScaleChainRelevantCountedStoppingDriverV2
open FamilyStickyScaleChainSelectedIdentityAutomaticAllLargeProducerV1
open FamilyStickyScaleChainSelectedIdentityDirectNormalizerProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyCapturedTubeBoxWidthV1

noncomputable section

/-!
# Recovered endpoint from the relevant counted stopping recursion

The relevant counted driver already constructs a terminal state, proves that
it has no literal relevant bad split, and retains the global-product estimate
at the first non-large interval.  These are exactly the two non-large inputs
of the paper-shaped recovered endpoint.  This file composes those theorems;
it does not re-assume either terminal no-split or the global-product bound.

The generic theorem leaves the all-large branch visible.  Its identity-cover
specialization discharges that branch with the automatic arbitrary-radius
Sticky endpoint.  The remaining hypotheses are the honest inputs not
produced by the counted recursion: a conditional canonical child successor,
the adjacent-card small-delta threshold, and room above the terminal profile.
-/

universe u

variable {delta : NNReal} {gapEpsilon targetExponent : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Generic coherent-cover outcome -/

/-- The relevant counted recursion closes the complete non-large branch.
No global-product or terminal-no-split premise remains: both are outputs of
the terminal counted state. -/
theorem relevantCanonicalCounting_allLarge_or_recoveredWitness
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : RelevantCanonicalChildSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (initial : RelevantCanonicalCountedState C N gapEpsilon eta)
    (strict_room : eta
        (relevantCanonicalCountingTerminalState C delta_pos delta_lt_one
          gap_pos eta_monotone exponent_budget successor initial).data.stage <
      targetExponent)
    (delta_le : delta <= firstNonLargeAdjacentCardThreshold iota gapEpsilon
      (eta
        ((relevantCanonicalCountingTerminalState C delta_pos delta_lt_one
          gap_pos eta_monotone exponent_budget successor initial).data.stage - 1))) :
    (relevantCanonicalCountingTerminalState C delta_pos delta_lt_one
        gap_pos eta_monotone exponent_budget successor initial).data.scales.AllStepsLarge
          gapEpsilon \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
        targetExponent
        (recoveredProfileV2 eta
          (relevantCanonicalCountingTerminalState C delta_pos delta_lt_one
            gap_pos eta_monotone exponent_budget successor initial).data.stage
          targetExponent)) := by
  let terminal := relevantCanonicalCountingTerminalState C delta_pos
    delta_lt_one gap_pos eta_monotone exponent_budget successor initial
  by_cases hall : terminal.data.scales.AllStepsLarge gapEpsilon
  · exact Or.inl hall
  · refine Or.inr
      (exists_twoExponentRecoveredLiteralWitnessV2_of_globalProduct_and_terminalNoSplit
        C (terminal.data.buffered C delta_pos) terminal.data.stage
        terminal.data.stage_pos terminal.data.stage_le eta_monotone two_le_zero
        ?_ hall ?_ ?_ gap_pos delta_pos ?_)
    · simpa [terminal] using strict_room
    · exact relevantCanonicalCountingTerminalState_actualGlobalProductAt_firstNonLarge_le
        C delta_pos delta_lt_one gap_pos eta_monotone exponent_budget successor
          initial hall
    · exact relevantCanonicalCountingTerminalState_terminalNoSplit
        C delta_pos delta_lt_one gap_pos eta_monotone exponent_budget successor
          initial hall
    · simpa [terminal] using delta_le

/-! ## Identity-cover Sticky endpoint -/

/-- For the identity coherent cover the all-large alternative is automatic
Sticky, while the non-large alternative is the recovered two-exponent
literal witness. -/
theorem identityRelevantCanonicalCounting_sticky_or_recoveredWitness
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : RelevantCanonicalChildSuccessor (N := N) (eta := eta)
      (identityRadiusCoherentCover fine) gap_pos.le delta_pos)
    (initial : RelevantCanonicalCountedState
      (identityRadiusCoherentCover fine) N gapEpsilon eta)
    (strict_room : eta
        (relevantCanonicalCountingTerminalState
          (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
          eta_monotone exponent_budget successor initial).data.stage <
      targetExponent)
    (delta_le : delta <= firstNonLargeAdjacentCardThreshold iota gapEpsilon
      (eta
        ((relevantCanonicalCountingTerminalState
          (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
          eta_monotone exponent_budget successor initial).data.stage - 1))) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal)) \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
        targetExponent
        (recoveredProfileV2 eta
          (relevantCanonicalCountingTerminalState
            (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
            eta_monotone exponent_budget successor initial).data.stage
          targetExponent)) := by
  let terminal := relevantCanonicalCountingTerminalState
    (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
      eta_monotone exponent_budget successor initial
  rcases relevantCanonicalCounting_allLarge_or_recoveredWitness
      (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
      eta_monotone two_le_zero exponent_budget successor initial strict_room
      delta_le with hall | witness
  · exact Or.inl
      (identityIsStickyAtEveryScale_of_allStepsLarge fine terminal.data.scales
        terminal.data.depth_pos delta_pos hall)
  · exact Or.inr witness

/-- Compatibility projection of the identity endpoint to the established V1
literal-witness API. -/
theorem identityRelevantCanonicalCounting_sticky_or_recoveredLiteralWitness
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (successor : RelevantCanonicalChildSuccessor (N := N) (eta := eta)
      (identityRadiusCoherentCover fine) gap_pos.le delta_pos)
    (initial : RelevantCanonicalCountedState
      (identityRadiusCoherentCover fine) N gapEpsilon eta)
    (strict_room : eta
        (relevantCanonicalCountingTerminalState
          (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
          eta_monotone exponent_budget successor initial).data.stage <
      targetExponent)
    (delta_le : delta <= firstNonLargeAdjacentCardThreshold iota gapEpsilon
      (eta
        ((relevantCanonicalCountingTerminalState
          (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
          eta_monotone exponent_budget successor initial).data.stage - 1))) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal)) \/
      Nonempty (KatzTaoDividingWitness delta N gapEpsilon
        (recoveredProfileV2 eta
          (relevantCanonicalCountingTerminalState
            (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
            eta_monotone exponent_budget successor initial).data.stage
          targetExponent)) := by
  rcases identityRelevantCanonicalCounting_sticky_or_recoveredWitness
      fine delta_pos delta_lt_one gap_pos eta_monotone two_le_zero
      exponent_budget successor initial strict_room delta_le with
    sticky | witness
  · exact Or.inl sticky
  · rcases witness with ⟨W⟩
    exact Or.inr ⟨W.toV1⟩

#print axioms relevantCanonicalCounting_allLarge_or_recoveredWitness
#print axioms identityRelevantCanonicalCounting_sticky_or_recoveredWitness
#print axioms identityRelevantCanonicalCounting_sticky_or_recoveredLiteralWitness

end
end FamilyStickyScaleChainRelevantCountedRecoveredEndpointV2
