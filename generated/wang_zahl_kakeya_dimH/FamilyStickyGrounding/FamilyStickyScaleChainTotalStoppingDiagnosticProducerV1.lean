import FamilyStickyGrounding.FamilyStickyScaleChainFirstNonLargeRelevantNodeProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainTotalStoppingDiagnosticProducerV1

open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainRootedRefinementTreeV1
open FamilyStickyScaleChainReservedExponentProfileV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
open FamilyStickyScaleChainActualSmallDeltaRecoveredEndpointV1
open FamilyStickyScaleChainActualStoppingUpstreamClosureV1
open FamilyStickyScaleChainDividingFiniteNodeProducerV1
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainFirstNonLargeRelevantNodeProducerV1

noncomputable section

/-!
# Total diagnostic for the finite scale-chain stopping process

This module performs every remaining stopping decision on the literal actual
quantities.  It first decides whether all adjacent intervals are large.  At
the first non-large interval it then checks the global product and adjacent
coarse value against their required powers, followed by the finite relevant
node search.

The success branch invokes the recovered relevant-node endpoint.  Each
failure branch retains the original strict reverse inequality or first-node
analytic alternative.  No global factor cap, active-parent collapse, or
caller-supplied finite-node certificate is assumed.
-/

universe u

variable {delta : NNReal} {epsilon : Real}
  {outerDepth chainDepth N : Nat}
  {S : FiniteScaleSequence delta outerDepth}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Canonical profiles used by every diagnostic branch -/

def diagnosticSelectedProfile
    (eta : Nat -> Real) (slot : Fin N) (epsilon : Real) : Nat -> Real :=
  reserveTailLoss eta (oneBasedStage slot)
    (halfReservedExponentRoom eta (oneBasedStage slot) epsilon)

def diagnosticRecoveredProfile
    (eta : Nat -> Real) (slot : Fin N) (epsilon : Real) : Nat -> Real :=
  recoveredReservedProfile eta (oneBasedStage slot)
    (halfReservedExponentRoom eta (oneBasedStage slot) epsilon)

/-! ## Exact failure payloads -/

/-- Eliminating the existing numerical failure record exposes exactly one of
the two strict failed comparisons, with both actual quantities retained. -/
theorem SelectedNumericalBudgetFailure.strictAlternative
    (B : BufferedChainFamily outerDepth chainDepth)
    (A : ActualIntervalCovers S)
    (profile : Nat -> Real) (stage : Nat) (m : Fin outerDepth)
    (F : SelectedNumericalBudgetFailure B A profile stage m) :
    requiredGlobalPowerAt S profile stage m < actualGlobalProductAt B m ∨
      requiredAdjacentPowerAt S profile stage m < A.adjacentCoarseValue m := by
  cases F with
  | global failed => exact Or.inl failed
  | adjacent failed => exact Or.inr failed

/-- Complete proof-relevant classification of the scale-chain stopping run.
The proof of `not_all_large` is stored in every dividing branch so that its
first interval is literally the same `firstNonLargeStep` used by all payloads. -/
inductive TotalStoppingDiagnostic
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (slot : Fin N) (eta : Nat -> Real) where
  | allLarge
      (all_large : S.AllStepsLarge epsilon)
  | recovered
      (not_all_large : Not (S.AllStepsLarge epsilon))
      (witness : KatzTaoDividingWitness delta N epsilon
        (diagnosticRecoveredProfile eta slot epsilon))
  | numericalFailure
      (not_all_large : Not (S.AllStepsLarge epsilon))
      (failure : SelectedNumericalBudgetFailure B
        (C.toActualIntervalCovers S)
        (diagnosticSelectedProfile eta slot epsilon)
        (oneBasedStage slot)
        (firstNonLargeStep S epsilon not_all_large))
  | relevantNodeFailure
      (not_all_large : Not (S.AllStepsLarge epsilon))
      (alternative : FirstRelevantNodeAnalyticAlternative
        (epsilon := epsilon)
        (profile := diagnosticSelectedProfile eta slot epsilon)
        (stage := oneBasedStage slot)
        (C.toActualIntervalCovers S) R
        (firstNonLargeStep S epsilon not_all_large))

/-! ## The total nested search -/

/-- Decide the complete stopping tree from actual values.  The only analytic
inputs are the room and small-delta hypotheses already required after a
successful finite search. -/
noncomputable def totalStoppingDiagnostic
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (slot : Fin N)
    (eta : Nat -> Real)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon)
    (delta_pos : 0 < delta)
    (delta_le : delta <=
      actualStrictLossRecoveredSmallDeltaThreshold
        eta (oneBasedStage slot) epsilon iota) :
    TotalStoppingDiagnostic (epsilon := epsilon) C R B slot eta := by
  classical
  by_cases all_large : S.AllStepsLarge epsilon
  · exact .allLarge all_large
  · let m := firstNonLargeStep S epsilon all_large
    let numerical := selectedNumericalBudgetSearch
      B (C.toActualIntervalCovers S)
      (diagnosticSelectedProfile eta slot epsilon)
      (oneBasedStage slot) m
    cases numerical with
    | inr failure =>
        exact .numericalFailure all_large failure
    | inl budgets =>
        let nodes := relevantNodeSearch
          (epsilon := epsilon)
          (profile := diagnosticSelectedProfile eta slot epsilon)
          (stage := oneBasedStage slot)
          (C.toActualIntervalCovers S) R m
        cases nodes with
        | inr failure =>
            exact .relevantNodeFailure all_large
              failure.toAnalyticAlternative
        | inl verified =>
            have budgets' : SelectedNumericalBudgets B
                (C.toActualIntervalCovers S)
                (reserveTailLoss eta (oneBasedStage slot)
                  (halfReservedExponentRoom eta
                    (oneBasedStage slot) epsilon))
                (oneBasedStage slot)
                (firstNonLargeStep S epsilon all_large) := by
              simpa [m, diagnosticSelectedProfile] using budgets.down
            have verified' : VerifiedRelevantStepNodeLowerBounds
                (epsilon := epsilon)
                (profile := reserveTailLoss eta (oneBasedStage slot)
                  (halfReservedExponentRoom eta
                    (oneBasedStage slot) epsilon))
                (stage := oneBasedStage slot)
                (C.toActualIntervalCovers S) R
                (firstNonLargeStep S epsilon all_large) := by
              simpa [m, diagnosticSelectedProfile] using verified.down
            have endpoint :=
              exists_recoveredLiteralWitness_of_relevantSelectedNumericalBudgets
                C R B slot eta_monotone two_le_zero strict_room all_large
                  budgets' verified' delta_pos delta_le
            let witness := Classical.choice endpoint
            exact .recovered all_large (by
              simpa [diagnosticRecoveredProfile] using witness)

/-! ## Shape theorems for downstream case analysis -/

/-- The total diagnostic always returns one of the four honest terminal
states; this theorem exposes a Prop-valued view for consumers that do not
need the proof-relevant payload object itself. -/
theorem totalStoppingDiagnostic_cases
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (slot : Fin N)
    (eta : Nat -> Real)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon)
    (delta_pos : 0 < delta)
    (delta_le : delta <=
      actualStrictLossRecoveredSmallDeltaThreshold
        eta (oneBasedStage slot) epsilon iota) :
    S.AllStepsLarge epsilon ∨
      Nonempty (KatzTaoDividingWitness delta N epsilon
        (diagnosticRecoveredProfile eta slot epsilon)) ∨
      (exists not_all_large : Not (S.AllStepsLarge epsilon),
        Nonempty (SelectedNumericalBudgetFailure B
          (C.toActualIntervalCovers S)
          (diagnosticSelectedProfile eta slot epsilon)
          (oneBasedStage slot)
          (firstNonLargeStep S epsilon not_all_large))) ∨
      exists not_all_large : Not (S.AllStepsLarge epsilon),
        Nonempty (FirstRelevantNodeAnalyticAlternative
          (epsilon := epsilon)
          (profile := diagnosticSelectedProfile eta slot epsilon)
          (stage := oneBasedStage slot)
          (C.toActualIntervalCovers S) R
          (firstNonLargeStep S epsilon not_all_large)) := by
  let result := totalStoppingDiagnostic C R B slot eta
    eta_monotone two_le_zero strict_room delta_pos delta_le
  cases result with
  | allLarge all_large => exact Or.inl all_large
  | recovered _ witness => exact Or.inr (Or.inl ⟨witness⟩)
  | numericalFailure not_all_large failure =>
      exact Or.inr (Or.inr (Or.inl ⟨not_all_large, ⟨failure⟩⟩))
  | relevantNodeFailure not_all_large alternative =>
      exact Or.inr (Or.inr (Or.inr ⟨not_all_large, ⟨alternative⟩⟩))

#print axioms SelectedNumericalBudgetFailure.strictAlternative
#print axioms totalStoppingDiagnostic
#print axioms totalStoppingDiagnostic_cases

end
end FamilyStickyScaleChainTotalStoppingDiagnosticProducerV1
