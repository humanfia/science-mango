import FamilyStickyGrounding.FamilyStickyScaleChainFixedLocalCardCountedDriverV2
import FamilyStickyGrounding.FamilyStickyScaleChainSelectedIdentityAutomaticAllLargeProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainFixedLocalCardRecoveredEndpointV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainDividingFiniteNodeProducerV1
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainTwoExponentStoppingCoreV2
open FamilyStickyScaleChainTwoParameterRecoveredEndpointV2
open FamilyStickyScaleChainTwoParameterTerminalNoSplitV2
open FamilyStickyScaleChainRelevantIntervalEnvelopeInvariantV2
open FamilyStickyScaleChainLocalCardAutomaticBoundsV2
open FamilyStickyScaleChainLocalCardBudgetInvariantV2
open FamilyStickyScaleChainFixedLocalCardCountedDriverV2
open FamilyStickyScaleChainSelectedIdentityAutomaticAllLargeProducerV1
open FamilyStickyScaleChainSelectedIdentityDirectNormalizerProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyCapturedTubeBoxWidthV1

noncomputable section

/-!
# Recovered endpoint with a fixed local-card budget

The fixed-local-card counted driver retains the two logical terminal facts
needed by the paper-shaped endpoint and, additionally, a bound `n` on the
active-fine cardinality at every non-large interval.  At the computed first
non-large interval this local bound controls the literal adjacent coarse
value.  Hence the adjacent small-delta threshold below depends on `n`, not on
the cardinality of the ambient index type.

The ambient cardinality remains present only in the established constant of
the identity-cover Sticky alternative.
-/

universe u

variable {delta : NNReal} {gapEpsilon targetExponent : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## A fixed-card minimum over stages `1, ..., N` -/

/-- Recursive minimum of the adjacent thresholds using one fixed natural
local-card bound `n`.  The successor step adds stage `k + 1`, whose
predecessor profile value is `eta k`. -/
def uniformFixedLocalAdjacentCardThreshold
    (n : Nat) (gapEpsilon : Real) (eta : Nat -> Real) : Nat -> NNReal
  | 0 => 1
  | k + 1 =>
      min (uniformFixedLocalAdjacentCardThreshold n gapEpsilon eta k)
        (adjacentCardBoundThreshold n gapEpsilon (eta k))

@[simp] theorem uniformFixedLocalAdjacentCardThreshold_zero
    (n : Nat) (gapEpsilon : Real) (eta : Nat -> Real) :
    uniformFixedLocalAdjacentCardThreshold n gapEpsilon eta 0 = 1 :=
  rfl

@[simp] theorem uniformFixedLocalAdjacentCardThreshold_succ
    (n : Nat) (gapEpsilon : Real) (eta : Nat -> Real) (k : Nat) :
    uniformFixedLocalAdjacentCardThreshold n gapEpsilon eta (k + 1) =
      min (uniformFixedLocalAdjacentCardThreshold n gapEpsilon eta k)
        (adjacentCardBoundThreshold n gapEpsilon (eta k)) :=
  rfl

/-- The finite fixed-card minimum is strictly positive. -/
theorem uniformFixedLocalAdjacentCardThreshold_pos
    (n : Nat) (gapEpsilon : Real) (eta : Nat -> Real) (N : Nat) :
    0 < uniformFixedLocalAdjacentCardThreshold n gapEpsilon eta N := by
  induction N with
  | zero => simp
  | succ k ih =>
      rw [uniformFixedLocalAdjacentCardThreshold_succ, lt_min_iff]
      exact
        ⟨ih, adjacentCardBoundThreshold_pos n gapEpsilon (eta k)⟩

/-- The minimum through `N` lies below every fixed-card factor indexed by
`k < N`. -/
theorem uniformFixedLocalAdjacentCardThreshold_le_index
    (n : Nat) (gapEpsilon : Real) (eta : Nat -> Real)
    (N k : Nat) (hk : k < N) :
    uniformFixedLocalAdjacentCardThreshold n gapEpsilon eta N <=
      adjacentCardBoundThreshold n gapEpsilon (eta k) := by
  induction N generalizing k with
  | zero => omega
  | succ j ih =>
      rw [uniformFixedLocalAdjacentCardThreshold_succ]
      by_cases hkj : k = j
      · subst k
        exact min_le_right _ _
      · have hkj_lt : k < j := by omega
        exact (min_le_left _ _).trans (ih k hkj_lt)

/-- Stage projection for every `stage` in `1..N`. -/
theorem uniformFixedLocalAdjacentCardThreshold_le_stage
    (n : Nat) (gapEpsilon : Real) (eta : Nat -> Real)
    (N stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N) :
    uniformFixedLocalAdjacentCardThreshold n gapEpsilon eta N <=
      adjacentCardBoundThreshold n gapEpsilon (eta (stage - 1)) := by
  apply uniformFixedLocalAdjacentCardThreshold_le_index
    n gapEpsilon eta N (stage - 1)
  omega

/-- The stage stored by every fixed-local-card counted state has the bounds
required by the uniform threshold. -/
theorem uniformFixedLocalAdjacentCardThreshold_le_countedStateStage
    (C : CoherentStickyMultiscaleCover fine) (cap : NNReal) (n : Nat)
    (X : RelevantFixedLocalCardCountedState
      C N gapEpsilon eta cap n) :
    uniformFixedLocalAdjacentCardThreshold n gapEpsilon eta N <=
      adjacentCardBoundThreshold n gapEpsilon
        (eta (X.counted.data.stage - 1)) := by
  exact uniformFixedLocalAdjacentCardThreshold_le_stage n gapEpsilon eta N
    X.counted.data.stage X.counted.data.stage_pos X.counted.data.stage_le

/-! ## Terminal-stage fixed-local-card endpoint -/

/-- The fixed-local-card recursion closes the non-large branch using only
its terminal global-product/no-split outputs and the carried local-card
budget.  In particular, the adjacent numerical comparison is rebuilt at the
literal first non-large interval from `activeFine.card <= n`. -/
theorem relevantFixedLocalCardCounting_allLarge_or_recoveredWitness
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal) (n : Nat)
    (stageWindow : RelevantFixedLocalCardStageWindow N eta cap n)
    (initial : RelevantFixedLocalCardCountedState
      C N gapEpsilon eta cap n)
    (strict_room : eta
        (relevantFixedLocalCardCountingTerminalState C delta_pos delta_lt_one
          gap_pos eta_monotone exponent_budget cap n stageWindow
          initial).counted.data.stage < targetExponent)
    (delta_le : delta <= adjacentCardBoundThreshold n gapEpsilon
      (eta
        ((relevantFixedLocalCardCountingTerminalState C delta_pos delta_lt_one
          gap_pos eta_monotone exponent_budget cap n stageWindow
          initial).counted.data.stage - 1))) :
    (relevantFixedLocalCardCountingTerminalState C delta_pos delta_lt_one
        gap_pos eta_monotone exponent_budget cap n stageWindow
        initial).counted.data.scales.AllStepsLarge gapEpsilon \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
        targetExponent
        (recoveredProfileV2 eta
          (relevantFixedLocalCardCountingTerminalState C delta_pos
            delta_lt_one gap_pos eta_monotone exponent_budget cap n
            stageWindow initial).counted.data.stage targetExponent)) := by
  let terminal := relevantFixedLocalCardCountingTerminalState C delta_pos
    delta_lt_one gap_pos eta_monotone exponent_budget cap n stageWindow initial
  by_cases hall : terminal.counted.data.scales.AllStepsLarge gapEpsilon
  · exact Or.inl hall
  · let m := firstNonLargeStep terminal.counted.data.scales gapEpsilon hall
    have m_not_large : Not
        (terminal.counted.data.scales.IsLarge gapEpsilon m) := by
      exact firstNonLargeStep_not_large terminal.counted.data.scales
        gapEpsilon hall
    have local_card_le : adjacentIntervalActiveFineCard C
        terminal.counted.data.scales m <= n :=
      terminal.localCardBudget m m_not_large
    have adjacent_le_n :
        (C.toActualIntervalCovers
          terminal.counted.data.scales).adjacentCoarseValue m <=
            (n : ENNReal) := by
      exact (actualAdjacentCoarseValue_le_intervalActiveFineCard C
        terminal.counted.data.scales m).trans (by
          exact_mod_cast local_card_le)
    have profile_pred_pos : 0 <
        selectedProfileV2 eta terminal.counted.data.stage targetExponent
          (terminal.counted.data.stage - 1) := by
      rw [selectedProfileV2_pred eta terminal.counted.data.stage_pos
        targetExponent]
      have eta_zero_le_pred :
          eta 0 <= eta (terminal.counted.data.stage - 1) :=
        eta_monotone (Nat.zero_le _)
      linarith
    have selected_delta_le : delta <= adjacentCardBoundThreshold n
        gapEpsilon
        (selectedProfileV2 eta terminal.counted.data.stage targetExponent
          (terminal.counted.data.stage - 1)) := by
      simpa [terminal,
        selectedProfileV2_pred eta terminal.counted.data.stage_pos
          targetExponent] using delta_le
    have selected_adjacent :
        (C.toActualIntervalCovers
          terminal.counted.data.scales).adjacentCoarseValue m <=
        requiredAdjacentPowerAt terminal.counted.data.scales
          (selectedProfileV2 eta terminal.counted.data.stage targetExponent)
          terminal.counted.data.stage m := by
      exact adjacentBudget_of_cardBound_long_and_smallDelta C
        terminal.counted.data.scales m
        (selectedProfileV2 eta terminal.counted.data.stage targetExponent)
        terminal.counted.data.stage n adjacent_le_n gap_pos profile_pred_pos
        delta_pos
        (firstNonLargeStep_isLong terminal.counted.data.scales gapEpsilon hall)
        selected_delta_le
    have global_eta :=
      relevantFixedLocalCardCountingTerminalState_actualGlobalProductAt_firstNonLarge_le
        C delta_pos delta_lt_one gap_pos eta_monotone exponent_budget cap n
          stageWindow initial hall
    have selected_global : actualGlobalProductAt
        (terminal.counted.data.buffered C delta_pos) m <=
      requiredGlobalPowerAt terminal.counted.data.scales
        (selectedProfileV2 eta terminal.counted.data.stage targetExponent)
        terminal.counted.data.stage m := by
      simpa [terminal, m, requiredGlobalPowerAt,
        selectedProfileV2_pred eta terminal.counted.data.stage_pos
          targetExponent] using global_eta
    have selected_budgets : SelectedNumericalBudgets
        (terminal.counted.data.buffered C delta_pos)
        (C.toActualIntervalCovers terminal.counted.data.scales)
        (selectedProfileV2 eta terminal.counted.data.stage targetExponent)
        terminal.counted.data.stage m :=
      ⟨selected_global, selected_adjacent⟩
    have terminal_no_split_eta :=
      relevantFixedLocalCardCountingTerminalState_terminalNoSplit C
        delta_pos delta_lt_one gap_pos eta_monotone exponent_budget cap n
          stageWindow initial hall
    have terminal_no_split_recovered : SelectedActualTerminalNoSplit
        (C.toActualIntervalCovers terminal.counted.data.scales) gapEpsilon
        (recoveredProfileV2 eta terminal.counted.data.stage targetExponent)
        terminal.counted.data.stage m := by
      exact (selectedActualTerminalNoSplit_recoveredProfileV2_iff
        (C.toActualIntervalCovers terminal.counted.data.scales)
        terminal.counted.data.stage m).2 (by
          simpa [terminal, m] using terminal_no_split_eta)
    refine Or.inr
      (exists_twoExponentRecoveredLiteralWitnessV2_of_selectedNumericalBudgets_and_terminalNoSplit
        C (terminal.counted.data.buffered C delta_pos)
        terminal.counted.data.stage terminal.counted.data.stage_pos
        terminal.counted.data.stage_le ?_ hall ?_ ?_)
    · simpa [terminal] using strict_room
    · simpa [m] using selected_budgets
    · simpa [m] using terminal_no_split_recovered

/-! ## Identity-cover endpoint at the terminal stage -/

/-- Identity-cover specialization: all-large gives the established Sticky
constant, while the non-large branch gives the recovered V2 witness. -/
theorem identityRelevantFixedLocalCardCounting_sticky_or_recoveredWitness
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal) (n : Nat)
    (stageWindow : RelevantFixedLocalCardStageWindow N eta cap n)
    (initial : RelevantFixedLocalCardCountedState
      (identityRadiusCoherentCover fine) N gapEpsilon eta cap n)
    (strict_room : eta
        (relevantFixedLocalCardCountingTerminalState
          (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
          eta_monotone exponent_budget cap n stageWindow
          initial).counted.data.stage < targetExponent)
    (delta_le : delta <= adjacentCardBoundThreshold n gapEpsilon
      (eta
        ((relevantFixedLocalCardCountingTerminalState
          (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
          eta_monotone exponent_budget cap n stageWindow
          initial).counted.data.stage - 1))) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal)) \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
        targetExponent
        (recoveredProfileV2 eta
          (relevantFixedLocalCardCountingTerminalState
            (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
            eta_monotone exponent_budget cap n stageWindow
            initial).counted.data.stage targetExponent)) := by
  let terminal := relevantFixedLocalCardCountingTerminalState
    (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
      eta_monotone exponent_budget cap n stageWindow initial
  rcases relevantFixedLocalCardCounting_allLarge_or_recoveredWitness
      (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
      eta_monotone two_le_zero exponent_budget cap n stageWindow initial
      strict_room delta_le with hall | witness
  · exact Or.inl
      (identityIsStickyAtEveryScale_of_allStepsLarge fine
        terminal.counted.data.scales terminal.counted.data.depth_pos delta_pos
        hall)
  · exact Or.inr witness

/-- Compatibility projection of the terminal-stage identity endpoint to the
V1 literal-witness API. -/
theorem identityRelevantFixedLocalCardCounting_sticky_or_recoveredLiteralWitness
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal) (n : Nat)
    (stageWindow : RelevantFixedLocalCardStageWindow N eta cap n)
    (initial : RelevantFixedLocalCardCountedState
      (identityRadiusCoherentCover fine) N gapEpsilon eta cap n)
    (strict_room : eta
        (relevantFixedLocalCardCountingTerminalState
          (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
          eta_monotone exponent_budget cap n stageWindow
          initial).counted.data.stage < targetExponent)
    (delta_le : delta <= adjacentCardBoundThreshold n gapEpsilon
      (eta
        ((relevantFixedLocalCardCountingTerminalState
          (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
          eta_monotone exponent_budget cap n stageWindow
          initial).counted.data.stage - 1))) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal)) \/
      Nonempty (KatzTaoDividingWitness delta N gapEpsilon
        (recoveredProfileV2 eta
          (relevantFixedLocalCardCountingTerminalState
            (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
            eta_monotone exponent_budget cap n stageWindow
            initial).counted.data.stage targetExponent)) := by
  rcases identityRelevantFixedLocalCardCounting_sticky_or_recoveredWitness
      fine delta_pos delta_lt_one gap_pos eta_monotone two_le_zero
      exponent_budget cap n stageWindow initial strict_room delta_le with
    sticky | witness
  · exact Or.inl sticky
  · rcases witness with ⟨W⟩
    exact Or.inr ⟨W.toV1⟩

/-! ## Uniform room and fixed-card threshold -/

/-- Generic endpoint with both terminal-stage numerical inputs fixed before
the recursion starts. -/
theorem relevantFixedLocalCardCounting_allLarge_or_recoveredWitness_of_uniformThreshold
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal) (n : Nat)
    (stageWindow : RelevantFixedLocalCardStageWindow N eta cap n)
    (initial : RelevantFixedLocalCardCountedState
      C N gapEpsilon eta cap n)
    (room_at_bound : eta N < targetExponent)
    (delta_le_uniform : delta <=
      uniformFixedLocalAdjacentCardThreshold n gapEpsilon eta N) :
    (relevantFixedLocalCardCountingTerminalState C delta_pos delta_lt_one
        gap_pos eta_monotone exponent_budget cap n stageWindow
        initial).counted.data.scales.AllStepsLarge gapEpsilon \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
        targetExponent
        (recoveredProfileV2 eta
          (relevantFixedLocalCardCountingTerminalState C delta_pos
            delta_lt_one gap_pos eta_monotone exponent_budget cap n
            stageWindow initial).counted.data.stage targetExponent)) := by
  let terminal := relevantFixedLocalCardCountingTerminalState C delta_pos
    delta_lt_one gap_pos eta_monotone exponent_budget cap n stageWindow initial
  have terminal_room : eta terminal.counted.data.stage < targetExponent :=
    (eta_monotone terminal.counted.data.stage_le).trans_lt room_at_bound
  have terminal_delta : delta <= adjacentCardBoundThreshold n gapEpsilon
      (eta (terminal.counted.data.stage - 1)) :=
    delta_le_uniform.trans
      (uniformFixedLocalAdjacentCardThreshold_le_stage n gapEpsilon eta N
        terminal.counted.data.stage terminal.counted.data.stage_pos
        terminal.counted.data.stage_le)
  exact relevantFixedLocalCardCounting_allLarge_or_recoveredWitness C
    delta_pos delta_lt_one gap_pos eta_monotone two_le_zero exponent_budget
      cap n stageWindow initial terminal_room terminal_delta

/-- Identity-cover fixed-local-card endpoint with its numerical endpoint
inputs precomputed uniformly over all stages. -/
theorem identityRelevantFixedLocalCardCounting_sticky_or_recoveredWitness_of_uniformThreshold
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal) (n : Nat)
    (stageWindow : RelevantFixedLocalCardStageWindow N eta cap n)
    (initial : RelevantFixedLocalCardCountedState
      (identityRadiusCoherentCover fine) N gapEpsilon eta cap n)
    (room_at_bound : eta N < targetExponent)
    (delta_le_uniform : delta <=
      uniformFixedLocalAdjacentCardThreshold n gapEpsilon eta N) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal)) \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
        targetExponent
        (recoveredProfileV2 eta
          (relevantFixedLocalCardCountingTerminalState
            (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
            eta_monotone exponent_budget cap n stageWindow
            initial).counted.data.stage targetExponent)) := by
  let terminal := relevantFixedLocalCardCountingTerminalState
    (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
      eta_monotone exponent_budget cap n stageWindow initial
  have terminal_room : eta terminal.counted.data.stage < targetExponent :=
    (eta_monotone terminal.counted.data.stage_le).trans_lt room_at_bound
  have terminal_delta : delta <= adjacentCardBoundThreshold n gapEpsilon
      (eta (terminal.counted.data.stage - 1)) :=
    delta_le_uniform.trans
      (uniformFixedLocalAdjacentCardThreshold_le_stage n gapEpsilon eta N
        terminal.counted.data.stage terminal.counted.data.stage_pos
        terminal.counted.data.stage_le)
  exact identityRelevantFixedLocalCardCounting_sticky_or_recoveredWitness fine
    delta_pos delta_lt_one gap_pos eta_monotone two_le_zero exponent_budget
      cap n stageWindow initial terminal_room terminal_delta

/-- V1 literal-witness projection of the uniform identity endpoint. -/
theorem identityRelevantFixedLocalCardCounting_sticky_or_recoveredLiteralWitness_of_uniformThreshold
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (cap : NNReal) (n : Nat)
    (stageWindow : RelevantFixedLocalCardStageWindow N eta cap n)
    (initial : RelevantFixedLocalCardCountedState
      (identityRadiusCoherentCover fine) N gapEpsilon eta cap n)
    (room_at_bound : eta N < targetExponent)
    (delta_le_uniform : delta <=
      uniformFixedLocalAdjacentCardThreshold n gapEpsilon eta N) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal)) \/
      Nonempty (KatzTaoDividingWitness delta N gapEpsilon
        (recoveredProfileV2 eta
          (relevantFixedLocalCardCountingTerminalState
            (identityRadiusCoherentCover fine) delta_pos delta_lt_one gap_pos
            eta_monotone exponent_budget cap n stageWindow
            initial).counted.data.stage targetExponent)) := by
  rcases
      identityRelevantFixedLocalCardCounting_sticky_or_recoveredWitness_of_uniformThreshold
        fine delta_pos delta_lt_one gap_pos eta_monotone two_le_zero
        exponent_budget cap n stageWindow initial room_at_bound
        delta_le_uniform with
    sticky | witness
  · exact Or.inl sticky
  · rcases witness with ⟨W⟩
    exact Or.inr ⟨W.toV1⟩

#print axioms uniformFixedLocalAdjacentCardThreshold_pos
#print axioms uniformFixedLocalAdjacentCardThreshold_le_index
#print axioms uniformFixedLocalAdjacentCardThreshold_le_stage
#print axioms uniformFixedLocalAdjacentCardThreshold_le_countedStateStage
#print axioms relevantFixedLocalCardCounting_allLarge_or_recoveredWitness
#print axioms identityRelevantFixedLocalCardCounting_sticky_or_recoveredWitness
#print axioms identityRelevantFixedLocalCardCounting_sticky_or_recoveredLiteralWitness
#print axioms relevantFixedLocalCardCounting_allLarge_or_recoveredWitness_of_uniformThreshold
#print axioms identityRelevantFixedLocalCardCounting_sticky_or_recoveredWitness_of_uniformThreshold
#print axioms identityRelevantFixedLocalCardCounting_sticky_or_recoveredLiteralWitness_of_uniformThreshold

end
end FamilyStickyScaleChainFixedLocalCardRecoveredEndpointV2
