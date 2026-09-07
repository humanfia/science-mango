import Family8Grounding.Family8ParentwiseBadParentPaperFactorTransitionV1
import Family8Grounding.Family8ParentwiseBadParentFiniteStageTerminationV1
import Mathlib.Tactic

/-!
# Finite runs of paper-factor bad-parent transitions

This module chains the literal one-step
`ParentwiseBadParentPaperFactorTransition` objects.  The chain is indexed by
`PaperFactorState`, so every intermediate actual factor list and its
structurally aligned readiness data are retained, and adjacent paper states
agree definitionally.

Every edge also carries a visible selector-stage certificate.  In
particular, `stage_strict` is not inferred from a fuel counter.  Forgetting
the paper data produces the already audited `BoundedBadParentRun`; all stage
bounds and accumulated radius/cardinality products are then reused without
changing a loss factor.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open scoped BigOperators ENNReal NNReal

namespace Family8PaperFactorFiniteRunV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperFactorStateV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseBadParentPaperFactorTransitionV1
open Family8ParentwiseBadParentRepeatedSuccessorLedgerV1
open Family8ParentwiseBadParentFiniteStageTerminationV1
open Family8ParentwiseBadParentMassAwareFactorListStateV2
open Family8StickySelectedFiberLowCFFreshRetentionProducerV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-! ## Exact scalar projection of one paper transition -/

/-- Forget the paper readiness fields of one genuine transition while
keeping its literal source/successor factor lists and every scalar loss.

The two list equalities stored in the paper transition are used only to
transport its concrete StateV2 theorems to the factors of the two paper
states. -/
def paperFactorProductStep
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {D : ActualTubeDatum delta iota}
    {S : StickyScaleCover D.family rho}
    {left right : List ActualFactorDatum}
    {hrho : 0 < rho} {hrhoOne : rho <= 1}
    {q : {q // q ∈ S.activeCoarse}}
    {lower C : ENNReal}
    {X : ParentwiseBadParentMassAwareFactorListState
      D S left right hrho hrhoOne q lower C}
    (T : ParentwiseBadParentPaperFactorTransition
      D S left right hrho hrhoOne q lower C X) :
    BadParentProductStep where
  sourceFactors := T.source.factors
  successorFactors := T.successor.factors
  uniformityLoss := C
  freshRetentionLoss :=
    badParentFreshRetentionLoss
      S hrho hrhoOne q X.base.selected lower
  source_radiusProduct_eq_fixedLoss_mul := by
    simpa only [T.source_factors_eq, T.successor_factors_eq] using
      T.source_radiusProduct_eq_fixedLoss_mul
  successor_cardProduct_le := by
    simpa only [T.source_factors_eq, T.successor_factors_eq] using
      T.successor_cardProduct_le
  source_cardProduct_le := by
    simpa only [T.source_factors_eq, T.successor_factors_eq] using
      T.source_cardProduct_le

@[simp] theorem paperFactorProductStep_sourceFactors
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {D : ActualTubeDatum delta iota}
    {S : StickyScaleCover D.family rho}
    {left right : List ActualFactorDatum}
    {hrho : 0 < rho} {hrhoOne : rho <= 1}
    {q : {q // q ∈ S.activeCoarse}}
    {lower C : ENNReal}
    {X : ParentwiseBadParentMassAwareFactorListState
      D S left right hrho hrhoOne q lower C}
    (T : ParentwiseBadParentPaperFactorTransition
      D S left right hrho hrhoOne q lower C X) :
    (paperFactorProductStep T).sourceFactors = T.source.factors :=
  rfl

@[simp] theorem paperFactorProductStep_successorFactors
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {D : ActualTubeDatum delta iota}
    {S : StickyScaleCover D.family rho}
    {left right : List ActualFactorDatum}
    {hrho : 0 < rho} {hrhoOne : rho <= 1}
    {q : {q // q ∈ S.activeCoarse}}
    {lower C : ENNReal}
    {X : ParentwiseBadParentMassAwareFactorListState
      D S left right hrho hrhoOne q lower C}
    (T : ParentwiseBadParentPaperFactorTransition
      D S left right hrho hrhoOne q lower C X) :
    (paperFactorProductStep T).successorFactors = T.successor.factors :=
  rfl

/-! ## The visible selector-stage obligation on a paper edge -/

/-- Stage information attached to one literal paper transition.  The strict
advance field is a named producer obligation and is never replaced by an
iteration counter. -/
structure PaperFactorStageTransitionCertificate
    (N sourceStage successorStage : Nat)
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {D : ActualTubeDatum delta iota}
    {S : StickyScaleCover D.family rho}
    {left right : List ActualFactorDatum}
    {hrho : 0 < rho} {hrhoOne : rho <= 1}
    {q : {q // q ∈ S.activeCoarse}}
    {lower C : ENNReal}
    {X : ParentwiseBadParentMassAwareFactorListState
      D S left right hrho hrhoOne q lower C}
    (T : ParentwiseBadParentPaperFactorTransition
      D S left right hrho hrhoOne q lower C X) where
  sourceStage_le : sourceStage <= N
  successorStage_le : successorStage <= N
  stage_strict : sourceStage < successorStage

namespace PaperFactorStageTransitionCertificate

/-- Forget paper readiness but retain the exact product step and all stage
facts expected by the bounded termination ledger. -/
def toBoundedTransition
    {N sourceStage successorStage : Nat}
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {D : ActualTubeDatum delta iota}
    {S : StickyScaleCover D.family rho}
    {left right : List ActualFactorDatum}
    {hrho : 0 < rho} {hrhoOne : rho <= 1}
    {q : {q // q ∈ S.activeCoarse}}
    {lower C : ENNReal}
    {X : ParentwiseBadParentMassAwareFactorListState
      D S left right hrho hrhoOne q lower C}
    {T : ParentwiseBadParentPaperFactorTransition
      D S left right hrho hrhoOne q lower C X}
    (H : PaperFactorStageTransitionCertificate
      N sourceStage successorStage T) :
    BadParentStageTransitionCertificate
      N sourceStage successorStage where
  productStep := paperFactorProductStep T
  sourceStage_le := H.sourceStage_le
  successorStage_le := H.successorStage_le
  stage_strict := H.stage_strict

end PaperFactorStageTransitionCertificate

/-! ## A finite chain retaining every paper state -/

/-- A finite chain of literal paper-factor transitions.

The `cons` constructor stores the genuine one-step transition itself.  Its
tail begins at exactly `transition.successor`, so the successor's actual
factor list and readiness object become definitionally the next source. -/
inductive PaperFactorFiniteRun (N : Nat) :
    Nat -> Nat -> PaperFactorState -> PaperFactorState -> Type 3
  | nil (stage : Nat) (state : PaperFactorState)
      (stage_le : stage <= N) :
      PaperFactorFiniteRun N stage stage state state
  | cons
      {sourceStage middleStage finalStage : Nat}
      {finalState : PaperFactorState}
      {delta rho : NNReal} {iota : Type}
      [Fintype iota] [DecidableEq iota]
      {D : ActualTubeDatum delta iota}
      {S : StickyScaleCover D.family rho}
      {left right : List ActualFactorDatum}
      {hrho : 0 < rho} {hrhoOne : rho <= 1}
      {q : {q // q ∈ S.activeCoarse}}
      {lower C : ENNReal}
      {X : ParentwiseBadParentMassAwareFactorListState
        D S left right hrho hrhoOne q lower C}
      (transition : ParentwiseBadParentPaperFactorTransition
        D S left right hrho hrhoOne q lower C X)
      (stageCertificate : PaperFactorStageTransitionCertificate
        N sourceStage middleStage transition)
      (tail : PaperFactorFiniteRun N middleStage finalStage
        transition.successor finalState) :
      PaperFactorFiniteRun N sourceStage finalStage
        transition.source finalState

namespace PaperFactorFiniteRun

/-- Forgetting paper states produces the definitionally composable bounded
run on their literal actual-factor lists. -/
def toBoundedBadParentRun
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : PaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState) :
    BoundedBadParentRun N sourceStage finalStage
      sourceState.factors finalState.factors := by
  induction run with
  | nil stage state stage_le =>
      exact .nil stage state.factors stage_le
  | cons transition stageCertificate tail ih =>
      exact .cons stageCertificate.toBoundedTransition ih

/-- The exact scalar ledger obtained from all stored paper transitions. -/
def productLedger
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : PaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState) :
    RepeatedBadParentLedger sourceState.factors finalState.factors :=
  run.toBoundedBadParentRun.toProductLedger

/-- Literal number of mathematical paper transitions. -/
def transitionCount
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : PaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState) : Nat :=
  run.toBoundedBadParentRun.transitionCount

/-- Trace of all paper states, each of which retains its dependent readiness
object and literal actual-factor list. -/
def states
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : PaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState) : List PaperFactorState := by
  induction run with
  | nil stage state stage_le => exact [state]
  | cons transition stageCertificate tail ih =>
      exact transition.source :: ih

/-- The actual-factor lists displayed by the retained paper-state trace. -/
def actualFactorListTrace
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : PaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState) : List (List ActualFactorDatum) :=
  run.states.map PaperFactorState.factors

/-- Every readiness object is retained together with the exact factor list
that indexes it. -/
def readinessTrace
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : PaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState) :
    List (Sigma PaperFactorReadinessList) :=
  run.states.map fun state =>
    ⟨state.factors, state.readiness⟩

/-! ## Termination and accumulated-loss consumers -/

/-- The actual paper-transition ledger contains at most `N` edges. -/
theorem productLedger_steps_length_le_N
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : PaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState) :
    run.productLedger.steps.length <= N := by
  exact run.toBoundedBadParentRun.productLedger_steps_length_le_N

/-- Requested weak finite-run bound. -/
theorem productLedger_steps_length_le_N_add_one
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : PaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState) :
    run.productLedger.steps.length <= N + 1 := by
  exact run.toBoundedBadParentRun.productLedger_steps_length_le_N_add_one

/-- Including the initial state, at most `N + 1` selector stages are
visited. -/
theorem visitedStageCount_le_N_add_one
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : PaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState) :
    run.transitionCount + 1 <= N + 1 := by
  exact run.toBoundedBadParentRun.visitedStageCount_le_N_add_one

/-- Finite termination plus the exact cumulative `(64/3)^steps`, `prod C`,
and `prod (C * L)` loss ledger for the retained paper-state chain. -/
theorem bounded_cumulative_exactProductCertificate
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : PaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState) :
    run.productLedger.steps.length <= N + 1 ∧
      factorRadiusProduct sourceState.factors =
        (64 / 3 : NNReal) ^ run.productLedger.steps.length *
          factorRadiusProduct finalState.factors ∧
      factorCardProduct finalState.factors <=
        (run.productLedger.steps.map
          (fun step => step.uniformityLoss)).prod *
            factorCardProduct sourceState.factors ∧
      factorCardProduct sourceState.factors <=
        (run.productLedger.steps.map (fun step =>
          step.uniformityLoss * step.freshRetentionLoss)).prod *
            factorCardProduct finalState.factors := by
  exact
    run.toBoundedBadParentRun.bounded_cumulative_exactProductCertificate

end PaperFactorFiniteRun

#print axioms paperFactorProductStep
#print axioms PaperFactorStageTransitionCertificate.toBoundedTransition
#print axioms PaperFactorFiniteRun.toBoundedBadParentRun
#print axioms PaperFactorFiniteRun.productLedger_steps_length_le_N_add_one
#print axioms PaperFactorFiniteRun.visitedStageCount_le_N_add_one
#print axioms PaperFactorFiniteRun.bounded_cumulative_exactProductCertificate

end
end Family8PaperFactorFiniteRunV1
