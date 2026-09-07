import Family8Grounding.Family8ParentwiseBadParentRepeatedSuccessorLedgerV1
import Family8Grounding.Family8ParentwiseNormalizedLongIntervalCoreSelectorV1
import Mathlib.Tactic

/-!
# Finite stage termination for repeated bad-parent successors

The normalized parentwise selector uses a literal natural-number stage with
`stage <= N`.  This file equips every genuine bad-parent product step with
the additional transition fact needed for iteration: its successor stage is
strictly larger than its source stage and both stages remain at most `N`.

That advancement fact is deliberately a named field of
`BadParentStageTransitionCertificate`.  The current one-step product state
does not hide or manufacture it.  In particular, the construction below is
not a fuel recursion: a run consists only of certified mathematical
transitions, and strict monotonicity proves that it contains at most `N`
transitions (hence at most `N + 1` visited stages).

Forgetting the stage certificates gives exactly the finite product ledger
from `Family8ParentwiseBadParentRepeatedSuccessorLedgerV1`, so the radius and
both cardinality losses are accumulated without any new approximation.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open scoped BigOperators ENNReal NNReal

namespace Family8ParentwiseBadParentFiniteStageTerminationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseBadParentRepeatedSuccessorLedgerV1

noncomputable section

/-! ## The explicit stage-advance obligation -/

/-- A genuine product successor together with its selector-stage transition.

The `stage_strict` field is the visible orchestration obligation: constructing
this certificate requires a proof that the successor really advances the
paper selector's stage. -/
structure BadParentStageTransitionCertificate
    (N sourceStage successorStage : Nat) where
  productStep : BadParentProductStep
  sourceStage_le : sourceStage <= N
  successorStage_le : successorStage <= N
  stage_strict : sourceStage < successorStage

/-! ## Definitionally composable certified runs -/

/-- A chain of actual bad-parent product steps whose selector stage strictly
advances at every edge.  Adjacent factor lists and adjacent stages agree
definitionally; there is no equality cast between successive steps. -/
inductive BoundedBadParentRun (N : Nat) :
    Nat -> Nat ->
      List ActualFactorDatum -> List ActualFactorDatum -> Type 2
  | nil (stage : Nat) (factors : List ActualFactorDatum)
      (stage_le : stage <= N) :
      BoundedBadParentRun N stage stage factors factors
  | cons {sourceStage middleStage finalStage : Nat}
      {finalFactors : List ActualFactorDatum}
      (transition : BadParentStageTransitionCertificate
        N sourceStage middleStage)
      (tail : BoundedBadParentRun N middleStage finalStage
        transition.productStep.successorFactors finalFactors) :
      BoundedBadParentRun N sourceStage finalStage
        transition.productStep.sourceFactors finalFactors

namespace BoundedBadParentRun

/-- Forget only the stage bookkeeping.  All product data and all one-step
losses are retained literally. -/
def toProductLedger
    {N sourceStage finalStage : Nat}
    {sourceFactors finalFactors : List ActualFactorDatum} :
    BoundedBadParentRun N sourceStage finalStage
      sourceFactors finalFactors ->
        RepeatedBadParentLedger sourceFactors finalFactors
  | .nil _ factors _ => .nil factors
  | .cons transition tail =>
      .cons transition.productStep tail.toProductLedger

/-- Number of certified transitions, not an externally supplied fuel. -/
def transitionCount
    {N sourceStage finalStage : Nat}
    {sourceFactors finalFactors : List ActualFactorDatum} :
    BoundedBadParentRun N sourceStage finalStage
      sourceFactors finalFactors -> Nat
  | .nil _ _ _ => 0
  | .cons _ tail => tail.transitionCount + 1

/-- Number of stages visited by a run, including its initial stage. -/
def visitedStageCount
    {N sourceStage finalStage : Nat}
    {sourceFactors finalFactors : List ActualFactorDatum}
    (run : BoundedBadParentRun N sourceStage finalStage
      sourceFactors finalFactors) : Nat :=
  run.transitionCount + 1

/-- A single certified transition forms a one-edge run. -/
def singleton
    {N sourceStage successorStage : Nat}
    (transition : BadParentStageTransitionCertificate
      N sourceStage successorStage) :
    BoundedBadParentRun N sourceStage successorStage
      transition.productStep.sourceFactors
      transition.productStep.successorFactors :=
  .cons transition
    (.nil successorStage transition.productStep.successorFactors
      transition.successorStage_le)

@[simp] theorem toProductLedger_stepCount
    {N sourceStage finalStage : Nat}
    {sourceFactors finalFactors : List ActualFactorDatum}
    (run : BoundedBadParentRun N sourceStage finalStage
      sourceFactors finalFactors) :
    run.toProductLedger.stepCount = run.transitionCount := by
  induction run with
  | nil stage factors stage_le => rfl
  | cons transition tail ih =>
      simp only [toProductLedger, RepeatedBadParentLedger.stepCount,
        transitionCount, ih]

/-- The initial stage of every certified run lies in the selector interval. -/
theorem sourceStage_le
    {N sourceStage finalStage : Nat}
    {sourceFactors finalFactors : List ActualFactorDatum}
    (run : BoundedBadParentRun N sourceStage finalStage
      sourceFactors finalFactors) :
    sourceStage <= N := by
  induction run with
  | nil stage factors stage_le => exact stage_le
  | cons transition tail ih => exact transition.sourceStage_le

/-- The terminal stage of every certified run lies in the selector interval. -/
theorem finalStage_le
    {N sourceStage finalStage : Nat}
    {sourceFactors finalFactors : List ActualFactorDatum}
    (run : BoundedBadParentRun N sourceStage finalStage
      sourceFactors finalFactors) :
    finalStage <= N := by
  induction run with
  | nil stage factors stage_le => exact stage_le
  | cons transition tail ih => exact ih

/-- Strict advancement spends at least one natural-number stage at each
transition.  This is the quantitative core of finite termination. -/
theorem sourceStage_add_transitionCount_le_finalStage
    {N sourceStage finalStage : Nat}
    {sourceFactors finalFactors : List ActualFactorDatum}
    (run : BoundedBadParentRun N sourceStage finalStage
      sourceFactors finalFactors) :
    sourceStage + run.transitionCount <= finalStage := by
  induction run with
  | nil stage factors stage_le =>
      simp only [transitionCount, Nat.add_zero]
      exact le_rfl
  | cons transition tail ih =>
      simp only [transitionCount]
      have hadvance := transition.stage_strict
      omega

/-- A run has at most `N` transitions.  This is stronger than the requested
`N + 1` bound because transitions are edges whereas selector stages are
vertices. -/
theorem transitionCount_le_N
    {N sourceStage finalStage : Nat}
    {sourceFactors finalFactors : List ActualFactorDatum}
    (run : BoundedBadParentRun N sourceStage finalStage
      sourceFactors finalFactors) :
    run.transitionCount <= N := by
  have hspan := run.sourceStage_add_transitionCount_le_finalStage
  have hfinal := run.finalStage_le
  omega

/-- The requested weak edge bound. -/
theorem transitionCount_le_N_add_one
    {N sourceStage finalStage : Nat}
    {sourceFactors finalFactors : List ActualFactorDatum}
    (run : BoundedBadParentRun N sourceStage finalStage
      sourceFactors finalFactors) :
    run.transitionCount <= N + 1 := by
  exact run.transitionCount_le_N.trans (Nat.le_succ N)

/-- Counting the initial stage as well, a certified run visits at most
`N + 1` selector stages. -/
theorem visitedStageCount_le_N_add_one
    {N sourceStage finalStage : Nat}
    {sourceFactors finalFactors : List ActualFactorDatum}
    (run : BoundedBadParentRun N sourceStage finalStage
      sourceFactors finalFactors) :
    run.visitedStageCount <= N + 1 := by
  unfold visitedStageCount
  exact Nat.succ_le_succ run.transitionCount_le_N

/-- The forgotten product ledger has exactly the certified transition count. -/
theorem productLedger_steps_length_eq_transitionCount
    {N sourceStage finalStage : Nat}
    {sourceFactors finalFactors : List ActualFactorDatum}
    (run : BoundedBadParentRun N sourceStage finalStage
      sourceFactors finalFactors) :
    run.toProductLedger.steps.length = run.transitionCount := by
  calc
    run.toProductLedger.steps.length = run.toProductLedger.stepCount :=
      (RepeatedBadParentLedger.stepCount_eq_steps_length
        run.toProductLedger).symm
    _ = run.transitionCount := run.toProductLedger_stepCount

/-- Thus the actual cumulative product ledger is itself bounded by `N`; no
separate recursion fuel is used. -/
theorem productLedger_steps_length_le_N
    {N sourceStage finalStage : Nat}
    {sourceFactors finalFactors : List ActualFactorDatum}
    (run : BoundedBadParentRun N sourceStage finalStage
      sourceFactors finalFactors) :
    run.toProductLedger.steps.length <= N := by
  rw [run.productLedger_steps_length_eq_transitionCount]
  exact run.transitionCount_le_N

/-- Requested `N + 1` finite-iteration statement for the product ledger. -/
theorem productLedger_steps_length_le_N_add_one
    {N sourceStage finalStage : Nat}
    {sourceFactors finalFactors : List ActualFactorDatum}
    (run : BoundedBadParentRun N sourceStage finalStage
      sourceFactors finalFactors) :
    run.toProductLedger.steps.length <= N + 1 := by
  exact run.productLedger_steps_length_le_N.trans (Nat.le_succ N)

/-! ## Finite termination connected to the exact accumulated losses -/

/-- A bounded certified run simultaneously supplies finite termination and
the exact accumulated radius, forward-cardinality, and reverse-cardinality
products from the repeated ledger. -/
theorem bounded_cumulative_exactProductCertificate
    {N sourceStage finalStage : Nat}
    {sourceFactors finalFactors : List ActualFactorDatum}
    (run : BoundedBadParentRun N sourceStage finalStage
      sourceFactors finalFactors) :
    run.toProductLedger.steps.length <= N + 1 ∧
      factorRadiusProduct sourceFactors =
        (64 / 3 : NNReal) ^ run.toProductLedger.steps.length *
          factorRadiusProduct finalFactors ∧
      factorCardProduct finalFactors <=
        (run.toProductLedger.steps.map
          (fun step => step.uniformityLoss)).prod *
            factorCardProduct sourceFactors ∧
      factorCardProduct sourceFactors <=
        (run.toProductLedger.steps.map (fun step =>
          step.uniformityLoss * step.freshRetentionLoss)).prod *
            factorCardProduct finalFactors := by
  refine ⟨run.productLedger_steps_length_le_N_add_one, ?_⟩
  exact run.toProductLedger.cumulative_exactProductCertificate

end BoundedBadParentRun

#print axioms BoundedBadParentRun.toProductLedger_stepCount
#print axioms BoundedBadParentRun.sourceStage_add_transitionCount_le_finalStage
#print axioms BoundedBadParentRun.transitionCount_le_N
#print axioms BoundedBadParentRun.visitedStageCount_le_N_add_one
#print axioms BoundedBadParentRun.productLedger_steps_length_le_N_add_one
#print axioms BoundedBadParentRun.bounded_cumulative_exactProductCertificate

end
end Family8ParentwiseBadParentFiniteStageTerminationV1
