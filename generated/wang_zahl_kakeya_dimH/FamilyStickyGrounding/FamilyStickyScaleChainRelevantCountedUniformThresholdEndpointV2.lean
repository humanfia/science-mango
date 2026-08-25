import FamilyStickyGrounding.FamilyStickyScaleChainRelevantCountedRecoveredEndpointV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainRelevantCountedUniformThresholdEndpointV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainFirstNonLargeAdjacentCardBudgetProducerV1
open FamilyStickyScaleChainTwoExponentStoppingCoreV2
open FamilyStickyScaleChainTwoParameterRecoveredEndpointV2
open FamilyStickyScaleChainRelevantIntervalEnvelopeInvariantV2
open FamilyStickyScaleChainRelevantCountedStoppingDriverV2
open FamilyStickyScaleChainRelevantCountedRecoveredEndpointV2
open FamilyStickyScaleChainSelectedIdentityAutomaticAllLargeProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyCapturedTubeBoxWidthV1

noncomputable section

/-!
# Uniform finite-stage threshold for the relevant counted endpoint

The recovered endpoint previously requested two numerical facts at the
computed terminal stage.  Since every counted state has stage in `1..N`, a
finite recursive minimum fixes the adjacent-card delta threshold before the
recursion is run.  Monotonicity of the profile similarly turns room at `N`
into room at the computed terminal stage.

The canonical successor and initial counted state remain explicit inputs.
-/

universe u

variable {delta : NNReal} {gapEpsilon targetExponent : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Explicit minimum over stages `1, ..., N` -/

/-- Recursive minimum of the adjacent-card thresholds at stages
`1, ..., N`.  The successor step adds the stage `n + 1`, whose predecessor
profile is `eta n`.  The value at `N = 0` is the harmless positive unit. -/
def uniformFirstNonLargeAdjacentCardThreshold
    (iota : Type*) [Fintype iota]
    (gapEpsilon : Real) (eta : Nat -> Real) : Nat -> NNReal
  | 0 => 1
  | n + 1 =>
      min (uniformFirstNonLargeAdjacentCardThreshold iota gapEpsilon eta n)
        (firstNonLargeAdjacentCardThreshold iota gapEpsilon (eta n))

@[simp] theorem uniformFirstNonLargeAdjacentCardThreshold_zero
    (iota : Type*) [Fintype iota]
    (gapEpsilon : Real) (eta : Nat -> Real) :
    uniformFirstNonLargeAdjacentCardThreshold iota gapEpsilon eta 0 = 1 :=
  rfl

@[simp] theorem uniformFirstNonLargeAdjacentCardThreshold_succ
    (iota : Type*) [Fintype iota]
    (gapEpsilon : Real) (eta : Nat -> Real) (n : Nat) :
    uniformFirstNonLargeAdjacentCardThreshold iota gapEpsilon eta (n + 1) =
      min (uniformFirstNonLargeAdjacentCardThreshold iota gapEpsilon eta n)
        (firstNonLargeAdjacentCardThreshold iota gapEpsilon (eta n)) :=
  rfl

/-- The finite recursive minimum remains strictly positive. -/
theorem uniformFirstNonLargeAdjacentCardThreshold_pos
    (iota : Type*) [Fintype iota]
    (gapEpsilon : Real) (eta : Nat -> Real) (N : Nat) :
    0 < uniformFirstNonLargeAdjacentCardThreshold
      iota gapEpsilon eta N := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [uniformFirstNonLargeAdjacentCardThreshold_succ, lt_min_iff]
      exact ⟨ih,
        firstNonLargeAdjacentCardThreshold_pos iota gapEpsilon (eta n)⟩

/-- The minimum through `N` lies below every factor indexed by `k < N`. -/
theorem uniformFirstNonLargeAdjacentCardThreshold_le_index
    (iota : Type*) [Fintype iota]
    (gapEpsilon : Real) (eta : Nat -> Real)
    (N k : Nat) (hk : k < N) :
    uniformFirstNonLargeAdjacentCardThreshold iota gapEpsilon eta N <=
      firstNonLargeAdjacentCardThreshold iota gapEpsilon (eta k) := by
  induction N generalizing k with
  | zero => omega
  | succ n ih =>
      rw [uniformFirstNonLargeAdjacentCardThreshold_succ]
      by_cases hkn : k = n
      · subst k
        exact min_le_right _ _
      · have hklt : k < n := by omega
        exact (min_le_left _ _).trans (ih k hklt)

/-- Stage-form projection: any stage in `1..N` receives its required
predecessor-profile threshold from the uniform minimum. -/
theorem uniformFirstNonLargeAdjacentCardThreshold_le_stage
    (iota : Type*) [Fintype iota]
    (gapEpsilon : Real) (eta : Nat -> Real)
    (N stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N) :
    uniformFirstNonLargeAdjacentCardThreshold iota gapEpsilon eta N <=
      firstNonLargeAdjacentCardThreshold iota gapEpsilon
        (eta (stage - 1)) := by
  apply uniformFirstNonLargeAdjacentCardThreshold_le_index
    iota gapEpsilon eta N (stage - 1)
  omega

/-- Every relevant counted state carries exactly the stage bounds needed by
the uniform-threshold projection. -/
theorem uniformFirstNonLargeAdjacentCardThreshold_le_countedStateStage
    (C : CoherentStickyMultiscaleCover fine)
    (X : RelevantCanonicalCountedState C N gapEpsilon eta) :
    uniformFirstNonLargeAdjacentCardThreshold iota gapEpsilon eta N <=
      firstNonLargeAdjacentCardThreshold iota gapEpsilon
        (eta (X.data.stage - 1)) := by
  exact uniformFirstNonLargeAdjacentCardThreshold_le_stage
    iota gapEpsilon eta N X.data.stage X.data.stage_pos X.data.stage_le

/-! ## Recovered endpoint with precomputed numerical inputs -/

/-- The generic coherent-cover endpoint with both terminal-stage numerical
inputs replaced by data fixed at the stage bound `N`. -/
theorem relevantCanonicalCounting_allLarge_or_recoveredWitness_of_uniformThreshold
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
    (room_at_bound : eta N < targetExponent)
    (delta_le_uniform : delta <=
      uniformFirstNonLargeAdjacentCardThreshold iota gapEpsilon eta N) :
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
  have terminal_room : eta terminal.data.stage < targetExponent :=
    (eta_monotone terminal.data.stage_le).trans_lt room_at_bound
  have terminal_delta : delta <=
      firstNonLargeAdjacentCardThreshold iota gapEpsilon
        (eta (terminal.data.stage - 1)) :=
    delta_le_uniform.trans
      (uniformFirstNonLargeAdjacentCardThreshold_le_countedStateStage
        (iota := iota) C terminal)
  exact relevantCanonicalCounting_allLarge_or_recoveredWitness
    C delta_pos delta_lt_one gap_pos eta_monotone two_le_zero
      exponent_budget successor initial terminal_room terminal_delta

/-! ## Identity-cover Sticky-or-witness endpoints -/

/-- Identity-cover endpoint with a delta threshold fixed before running the
counted recursion.  The successor and initial state remain explicit. -/
theorem identityRelevantCanonicalCounting_sticky_or_recoveredWitness_of_uniformThreshold
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
          (relevantCanonicalCountingTerminalState
            (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
            eta_monotone exponent_budget successor initial).data.stage
          targetExponent)) := by
  let terminal := relevantCanonicalCountingTerminalState
    (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
      eta_monotone exponent_budget successor initial
  have terminal_room : eta terminal.data.stage < targetExponent :=
    (eta_monotone terminal.data.stage_le).trans_lt room_at_bound
  have terminal_delta : delta <=
      firstNonLargeAdjacentCardThreshold iota gapEpsilon
        (eta (terminal.data.stage - 1)) :=
    delta_le_uniform.trans
      (uniformFirstNonLargeAdjacentCardThreshold_le_countedStateStage
        (iota := iota) (identityRadiusCoherentCover fine) terminal)
  exact identityRelevantCanonicalCounting_sticky_or_recoveredWitness
    fine delta_pos delta_lt_one gap_pos eta_monotone two_le_zero
      exponent_budget successor initial terminal_room terminal_delta

/-- Compatibility projection of the uniform identity endpoint to the V1
literal-witness API. -/
theorem identityRelevantCanonicalCounting_sticky_or_recoveredLiteralWitness_of_uniformThreshold
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
    (room_at_bound : eta N < targetExponent)
    (delta_le_uniform : delta <=
      uniformFirstNonLargeAdjacentCardThreshold iota gapEpsilon eta N) :
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
  rcases
      identityRelevantCanonicalCounting_sticky_or_recoveredWitness_of_uniformThreshold
        fine delta_pos delta_lt_one gap_pos eta_monotone two_le_zero
        exponent_budget successor initial room_at_bound delta_le_uniform with
    sticky | witness
  · exact Or.inl sticky
  · rcases witness with ⟨W⟩
    exact Or.inr ⟨W.toV1⟩

#print axioms uniformFirstNonLargeAdjacentCardThreshold_pos
#print axioms uniformFirstNonLargeAdjacentCardThreshold_le_index
#print axioms uniformFirstNonLargeAdjacentCardThreshold_le_stage
#print axioms uniformFirstNonLargeAdjacentCardThreshold_le_countedStateStage
#print axioms relevantCanonicalCounting_allLarge_or_recoveredWitness_of_uniformThreshold
#print axioms identityRelevantCanonicalCounting_sticky_or_recoveredWitness_of_uniformThreshold
#print axioms identityRelevantCanonicalCounting_sticky_or_recoveredLiteralWitness_of_uniformThreshold

end
end FamilyStickyScaleChainRelevantCountedUniformThresholdEndpointV2
