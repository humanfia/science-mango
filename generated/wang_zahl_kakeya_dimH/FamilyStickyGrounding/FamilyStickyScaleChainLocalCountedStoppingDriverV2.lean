import FamilyStickyGrounding.FamilyStickyScaleChainLastStageCountingBoundV2
import FamilyStickyGrounding.FamilyStickyScaleChainLocalSuccessorAssemblerV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace FamilyStickyScaleChainLocalCountedStoppingDriverV2

open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainDividingFiniteNodeProducerV1
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainFirstNonLargeAdjacentCardBudgetProducerV1
open FamilyStickyScaleChainHierarchyGlobalEnvelopeV2
open FamilyStickyScaleChainTwoExponentStoppingCoreV2
open FamilyStickyScaleChainTwoParameterRecoveredEndpointV2
open FamilyStickyScaleChainTwoParameterTerminalNoSplitV2
open FamilyStickyScaleChainBoundedRecursiveStoppingV2
open FamilyStickyScaleChainHierarchyRecursiveStoppingDriverV2
open FamilyStickyScaleChainLocalSuccessorAssemblerV2
open FamilyStickyScaleChainLastStageCountingBoundV2

noncomputable section

/-!
# Local counted stopping driver

This module is the thin composition layer between the local hierarchy
replacement contract and the factor-count-backed stopping driver.  Its public
successor input is `LocalHierarchyAnalyticSuccessor`: unchanged intervals are
transported automatically, and only the two children require new envelope
bounds.  The factor-count invariant proves last-stage termination, so no
`NoBadAtStageBound` input appears here.

The local successor is still an explicit structural/analytic input; this
module does not manufacture a hierarchy realization tied to the original
fine family.  All numerical assumptions used by counting and by the optional
recovered endpoint remain visible in theorem signatures.
-/

universe u

variable {delta : NNReal} {gapEpsilon targetExponent : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Local-to-global successor composition -/

/-- Assemble the all-interval hierarchy successor from the local replacement
contract.  This is the only conversion used by the counted driver below. -/
def hierarchySuccessorOfLocal
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (successor : LocalHierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos) :
    HierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos :=
  LocalHierarchyAnalyticSuccessor.toHierarchyAnalyticSuccessor
    C gap_pos.le delta_pos eta_monotone successor

/-- The local counted successor.  Its only non-numerical input is the local
replacement contract; last-stage exclusion is derived by factor counting. -/
def localCountingNext
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (eta_monotone : Monotone eta)
    (successor : LocalHierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (X : FactorCountState delta N gapEpsilon eta) :
    Option (FactorCountState delta N gapEpsilon eta) :=
  countingNext C delta_pos delta_lt_one gap_pos exponent_budget
    (hierarchySuccessorOfLocal C delta_pos gap_pos eta_monotone successor) X

/-- The local successor stops exactly when no literal actual bad split
exists. -/
theorem localCountingNext_eq_none_iff_no_bad
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (eta_monotone : Monotone eta)
    (successor : LocalHierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (X : FactorCountState delta N gapEpsilon eta) :
    localCountingNext C delta_pos delta_lt_one gap_pos exponent_budget
      eta_monotone successor X = none <->
        Not (Nonempty (SelectedActualBadSplit C X.1)) := by
  exact countingNext_eq_none_iff_no_bad C delta_pos delta_lt_one gap_pos
    exponent_budget
    (hierarchySuccessorOfLocal C delta_pos gap_pos eta_monotone successor) X

/-- The local counted hierarchy driver is the factor-count-backed bounded
system specialized to the assembled local successor. -/
def localCountingBoundedSystem
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (eta_monotone : Monotone eta)
    (successor : LocalHierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos) :
    BoundedSuccessorSystem (FactorCountState delta N gapEpsilon eta) N :=
  countingBoundedSystem C delta_pos delta_lt_one gap_pos exponent_budget
    (hierarchySuccessorOfLocal C delta_pos gap_pos eta_monotone successor)


/-! ## Counted terminal state -/

/-- The canonical terminal state computed from a stage-history-valid input. -/
def localCountedTerminalState
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (eta_monotone : Monotone eta)
    (successor : LocalHierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (initial : FactorCountState delta N gapEpsilon eta) :
    FactorCountState delta N gapEpsilon eta :=
  (localCountingBoundedSystem C delta_pos delta_lt_one gap_pos
    exponent_budget eta_monotone successor).terminalState initial

/-- The computed state is terminal for the local counted successor. -/
theorem localCountingNext_terminalState_eq_none
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (eta_monotone : Monotone eta)
    (successor : LocalHierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (initial : FactorCountState delta N gapEpsilon eta) :
    localCountingNext C delta_pos delta_lt_one gap_pos exponent_budget
      eta_monotone successor
      (localCountedTerminalState C delta_pos delta_lt_one gap_pos
        exponent_budget eta_monotone successor initial) = none := by
  exact (localCountingBoundedSystem C delta_pos delta_lt_one gap_pos
    exponent_budget eta_monotone successor).next_terminalState_eq_none initial

/-- The counted terminal state is reached in at most the initial remaining
stage budget.  The factor-count history invariant is carried by every state
in this reachability relation. -/
theorem localCountedTerminalState_reachesIn
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (eta_monotone : Monotone eta)
    (successor : LocalHierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (initial : FactorCountState delta N gapEpsilon eta) :
    exists steps, steps <= N - initial.1.stage /\
      (localCountingBoundedSystem C delta_pos delta_lt_one gap_pos
        exponent_budget eta_monotone successor).ReachesIn steps initial
          (localCountedTerminalState C delta_pos delta_lt_one gap_pos
            exponent_budget eta_monotone successor initial) := by
  exact (localCountingBoundedSystem C delta_pos delta_lt_one gap_pos
    exponent_budget eta_monotone successor).terminalState_reachesIn initial

/-- The counted terminal state contains no literal actual bad split. -/
theorem localCountedTerminalState_no_bad
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (eta_monotone : Monotone eta)
    (successor : LocalHierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (initial : FactorCountState delta N gapEpsilon eta) :
    Not (Nonempty (SelectedActualBadSplit C
      (localCountedTerminalState C delta_pos delta_lt_one gap_pos
        exponent_budget eta_monotone successor initial).1)) := by
  exact (localCountingNext_eq_none_iff_no_bad C delta_pos delta_lt_one
    gap_pos exponent_budget eta_monotone successor _).1
      (localCountingNext_terminalState_eq_none C delta_pos delta_lt_one
        gap_pos exponent_budget eta_monotone successor initial)

/-- On every non-all-large branch, the counted terminal state satisfies the
literal selected actual terminal no-split predicate. -/
theorem localCountedTerminalState_terminalNoSplit
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (eta_monotone : Monotone eta)
    (successor : LocalHierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (initial : FactorCountState delta N gapEpsilon eta) :
    forall not_all_large : Not
        ((localCountedTerminalState C delta_pos delta_lt_one gap_pos
          exponent_budget eta_monotone successor initial).1.scales.AllStepsLarge
            gapEpsilon),
      SelectedActualTerminalNoSplit
        (C.toActualIntervalCovers
          (localCountedTerminalState C delta_pos delta_lt_one gap_pos
            exponent_budget eta_monotone successor initial).1.scales)
        gapEpsilon eta
        (localCountedTerminalState C delta_pos delta_lt_one gap_pos
          exponent_budget eta_monotone successor initial).1.stage
        (firstNonLargeStep
          (localCountedTerminalState C delta_pos delta_lt_one gap_pos
            exponent_budget eta_monotone successor initial).1.scales
          gapEpsilon not_all_large) := by
  exact (no_bad_iff_terminalNoSplit C _).1
    (localCountedTerminalState_no_bad C delta_pos delta_lt_one gap_pos
      exponent_budget eta_monotone successor initial)

/-- Exact terminal classification for the local counted run. -/
theorem localCountedTerminalState_allLarge_or_terminalNoSplit
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (eta_monotone : Monotone eta)
    (successor : LocalHierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (initial : FactorCountState delta N gapEpsilon eta) :
    let terminal := localCountedTerminalState C delta_pos delta_lt_one gap_pos
      exponent_budget eta_monotone successor initial
    terminal.1.scales.AllStepsLarge gapEpsilon \/
      exists not_all_large : Not
          (terminal.1.scales.AllStepsLarge gapEpsilon),
        SelectedActualTerminalNoSplit
          (C.toActualIntervalCovers terminal.1.scales)
          gapEpsilon eta terminal.1.stage
          (firstNonLargeStep terminal.1.scales gapEpsilon not_all_large) := by
  let terminal := localCountedTerminalState C delta_pos delta_lt_one gap_pos
    exponent_budget eta_monotone successor initial
  change terminal.1.scales.AllStepsLarge gapEpsilon \/
    exists not_all_large : Not (terminal.1.scales.AllStepsLarge gapEpsilon),
      SelectedActualTerminalNoSplit
        (C.toActualIntervalCovers terminal.1.scales)
        gapEpsilon eta terminal.1.stage
        (firstNonLargeStep terminal.1.scales gapEpsilon not_all_large)
  by_cases all_large : terminal.1.scales.AllStepsLarge gapEpsilon
  · exact Or.inl all_large
  · right
    refine ⟨all_large, ?_⟩
    simpa only [terminal] using
      localCountedTerminalState_terminalNoSplit C delta_pos delta_lt_one
        gap_pos exponent_budget eta_monotone successor initial all_large


/-! ## Optional recovered two-exponent endpoint -/

/-- A stopped local counted state feeds the existing recovered endpoint. -/
theorem allLarge_or_twoExponentWitness_of_localCountingNext_eq_none
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (eta_monotone : Monotone eta)
    (successor : LocalHierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (X : FactorCountState delta N gapEpsilon eta)
    (hterminal : localCountingNext C delta_pos delta_lt_one gap_pos
      exponent_budget eta_monotone successor X = none)
    (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta X.1.stage < targetExponent)
    (delta_le : delta <= firstNonLargeAdjacentCardThreshold iota gapEpsilon
      (eta (X.1.stage - 1))) :
    X.1.scales.AllStepsLarge gapEpsilon \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
        targetExponent
        (recoveredProfileV2 eta X.1.stage targetExponent)) := by
  have no_bad : Not (Nonempty (SelectedActualBadSplit C X.1)) :=
    (localCountingNext_eq_none_iff_no_bad C delta_pos delta_lt_one gap_pos
      exponent_budget eta_monotone successor X).1 hterminal
  by_cases all_large : X.1.scales.AllStepsLarge gapEpsilon
  · exact Or.inl all_large
  · right
    have terminalNoSplit : SelectedActualTerminalNoSplit
        (C.toActualIntervalCovers X.1.scales) gapEpsilon eta X.1.stage
        (firstNonLargeStep X.1.scales gapEpsilon all_large) :=
      (no_bad_iff_terminalNoSplit C X.1).1 no_bad all_large
    have globalProduct : actualGlobalProductAt X.1.buffered
          (firstNonLargeStep X.1.scales gapEpsilon all_large) <=
        requiredGlobalPowerAt X.1.scales eta X.1.stage
          (firstNonLargeStep X.1.scales gapEpsilon all_large) := by
      exact (actualGlobalProductAt_le_hierarchyGlobalEnvelopeAt X.1.buffered
        (firstNonLargeStep X.1.scales gapEpsilon all_large)).trans
          (X.1.globalEnvelope_upper
            (firstNonLargeStep X.1.scales gapEpsilon all_large))
    exact
      exists_twoExponentRecoveredLiteralWitnessV2_of_globalProduct_and_terminalNoSplit
        C X.1.buffered X.1.stage X.1.stage_pos X.1.stage_le eta_monotone
        two_le_zero strict_room all_large globalProduct terminalNoSplit
        gap_pos delta_pos delta_le

/-- Recovered two-exponent endpoint for the computed local counted terminal
state.  Every counting and endpoint hypothesis remains explicit. -/
theorem localCountedTerminalState_allLarge_or_twoExponentWitness
    (C : CoherentStickyMultiscaleCover fine)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (gap_pos : 0 < gapEpsilon)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (eta_monotone : Monotone eta)
    (successor : LocalHierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_pos.le delta_pos)
    (initial : FactorCountState delta N gapEpsilon eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta
      (localCountedTerminalState C delta_pos delta_lt_one gap_pos
        exponent_budget eta_monotone successor initial).1.stage < targetExponent)
    (delta_le : delta <= firstNonLargeAdjacentCardThreshold iota gapEpsilon
      (eta ((localCountedTerminalState C delta_pos delta_lt_one gap_pos
        exponent_budget eta_monotone successor initial).1.stage - 1))) :
    let terminal := localCountedTerminalState C delta_pos delta_lt_one gap_pos
      exponent_budget eta_monotone successor initial
    terminal.1.scales.AllStepsLarge gapEpsilon \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
        targetExponent
        (recoveredProfileV2 eta terminal.1.stage targetExponent)) := by
  exact allLarge_or_twoExponentWitness_of_localCountingNext_eq_none
    C delta_pos delta_lt_one gap_pos exponent_budget eta_monotone successor
    (localCountedTerminalState C delta_pos delta_lt_one gap_pos
      exponent_budget eta_monotone successor initial)
    (localCountingNext_terminalState_eq_none C delta_pos delta_lt_one gap_pos
      exponent_budget eta_monotone successor initial)
    two_le_zero strict_room delta_le

#print axioms hierarchySuccessorOfLocal
#print axioms localCountingNext_eq_none_iff_no_bad
#print axioms localCountingNext_terminalState_eq_none
#print axioms localCountedTerminalState_reachesIn
#print axioms localCountedTerminalState_terminalNoSplit
#print axioms localCountedTerminalState_allLarge_or_twoExponentWitness


end
end FamilyStickyScaleChainLocalCountedStoppingDriverV2
