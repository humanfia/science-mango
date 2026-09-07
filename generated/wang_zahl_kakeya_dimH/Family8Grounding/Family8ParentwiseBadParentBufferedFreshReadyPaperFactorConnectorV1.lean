import Family8Grounding.Family8BadParentFreshBufferedActualHierarchyReadinessV1
import Family8Grounding.Family8PaperFactorFiniteRunV1
import Family8Grounding.Family8ParentwiseBadParentPaperFactorTransitionV1
import Mathlib.Tactic

/-!
# Buffered same-selected fresh readiness for paper-factor traces

This connector sends the actual buffered fresh hierarchy directly to the
paper-factor transition.  The fresh readiness is pinned to the literal
`X.base.selected` in the same `q`-fibre.  It is neither re-selected nor routed
through the older unbuffered readiness record.  Readiness for the unchanged,
source, and coarse atoms remains explicit.

The trace is stage-free: it records only supplied mathematical transitions
and their exact radius/cardinality product ledger.  The carrier-nesting proof
is consumed once by the buffered readiness package and is not reintroduced as
an independent premise here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open scoped BigOperators ENNReal NNReal

namespace Family8ParentwiseBadParentBufferedFreshReadyPaperFactorConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8BadParentFreshReadinessV1
open Family8BadParentFreshBufferedActualHierarchyReadinessV1
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperFactorFiniteRunV1
open Family8PaperFactorStateV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentMassAwareFactorListStateV2
open Family8ParentwiseBadParentPaperFactorTransitionV1
open Family8ParentwiseBadParentRepeatedSuccessorLedgerV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta tau rho : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  {source : UniformTubeFamily delta sourceIndex}

/-- The literal lower-endpoint datum used by both the source interval and the
paper-factor transition. -/
def badParentBufferedIntervalSourceDatum
    (C : CoherentStickyMultiscaleCover source)
    (tau rho : NNReal) (hdeltaTau : delta <= tau)
    (hTauRho : tau <= rho) (hRhoOne : rho <= 1)
    (Y : Shading
      (C.base.cover tau hdeltaTau
        (hTauRho.trans hRhoOne)).coarse.bodyFamily) :
    ActualTubeDatum tau
      (Fin (C.base.cover tau hdeltaTau
        (hTauRho.trans hRhoOne)).coarseCard) where
  family :=
    (C.base.cover tau hdeltaTau
      (hTauRho.trans hRhoOne)).coarse
  shading := Y

/-- Build the literal paper-factor transition by feeding the buffered fresh
readiness directly to the generic transition constructor. -/
def parentwiseBadParentPaperFactorTransition_of_bufferedFreshReadiness
    (Csource : CoherentStickyMultiscaleCover source)
    {epsilon : Real} (hdeltaPos : 0 < delta) (hepsilon : 0 < epsilon)
    (tau rho : NNReal) (hdeltaTau : delta <= tau)
    (hTauRho : tau <= rho) (hRhoOne : rho <= 1)
    (Y : Shading
      (Csource.base.cover tau hdeltaTau
        (hTauRho.trans hRhoOne)).coarse.bodyFamily)
    (hrho : 0 < rho)
    (q : {q // q ∈
      (badParentSourceIntervalCover Csource tau rho
        hdeltaTau hTauRho hRhoOne).activeCoarse})
    (left right : List ActualFactorDatum)
    (lower factorC : ENNReal)
    (X : ParentwiseBadParentMassAwareFactorListState
      (badParentBufferedIntervalSourceDatum Csource tau rho
        hdeltaTau hTauRho hRhoOne Y)
      (badParentSourceIntervalCover Csource tau rho
        hdeltaTau hTauRho hRhoOne)
      left right hrho hRhoOne q lower factorC)
    (leftReadiness : PaperFactorReadinessList left)
    (sourceAtomReadiness : PaperFactorAtomReadiness
      (badParentActiveFineSourceAtom
        (badParentBufferedIntervalSourceDatum Csource tau rho
          hdeltaTau hTauRho hRhoOne Y)
        (badParentSourceIntervalCover Csource tau rho
          hdeltaTau hTauRho hRhoOne)))
    (rightReadiness : PaperFactorReadinessList right)
    (coarseAtomReadiness : PaperFactorAtomReadiness
      (badParentCoarseAtom
        (badParentBufferedIntervalSourceDatum Csource tau rho
          hdeltaTau hTauRho hRhoOne Y)
        (badParentSourceIntervalCover Csource tau rho
          hdeltaTau hTauRho hRhoOne)))
    (freshReadiness : BadParentFreshBufferedActualHierarchyReadiness
      Csource tau rho hdeltaTau hTauRho hRhoOne Y hrho q
        X.base.selected epsilon hdeltaPos hepsilon) :
    ParentwiseBadParentPaperFactorTransition
      (badParentBufferedIntervalSourceDatum Csource tau rho
        hdeltaTau hTauRho hRhoOne Y)
      (badParentSourceIntervalCover Csource tau rho
        hdeltaTau hTauRho hRhoOne)
      left right hrho hRhoOne q lower factorC X := by
  exact parentwiseBadParentPaperFactorTransition
    (badParentBufferedIntervalSourceDatum Csource tau rho
      hdeltaTau hTauRho hRhoOne Y)
    (badParentSourceIntervalCover Csource tau rho
      hdeltaTau hTauRho hRhoOne)
    left right hrho hRhoOne q lower factorC X
    leftReadiness sourceAtomReadiness rightReadiness coarseAtomReadiness
    freshReadiness.toPaperFactorAtomReadiness

/-- All readiness data for one buffered, same-selected paper-factor edge. -/
structure SameSelectedBufferedFreshReadyPaperFactorStep
    (Csource : CoherentStickyMultiscaleCover source)
    (tau rho : NNReal) (hdeltaTau : delta <= tau)
    (hTauRho : tau <= rho) (hRhoOne : rho <= 1)
    (Y : Shading
      (Csource.base.cover tau hdeltaTau
        (hTauRho.trans hRhoOne)).coarse.bodyFamily)
    (hrho : 0 < rho)
    (q : {q // q ∈
      (badParentSourceIntervalCover Csource tau rho
        hdeltaTau hTauRho hRhoOne).activeCoarse})
    (left right : List ActualFactorDatum)
    (lower factorC : ENNReal)
    (X : ParentwiseBadParentMassAwareFactorListState
      (badParentBufferedIntervalSourceDatum Csource tau rho
        hdeltaTau hTauRho hRhoOne Y)
      (badParentSourceIntervalCover Csource tau rho
        hdeltaTau hTauRho hRhoOne)
      left right hrho hRhoOne q lower factorC)
    (epsilon : Real) (hdeltaPos : 0 < delta)
    (hepsilon : 0 < epsilon) where
  leftReadiness : PaperFactorReadinessList left
  sourceAtomReadiness : PaperFactorAtomReadiness
    (badParentActiveFineSourceAtom
      (badParentBufferedIntervalSourceDatum Csource tau rho
        hdeltaTau hTauRho hRhoOne Y)
      (badParentSourceIntervalCover Csource tau rho
        hdeltaTau hTauRho hRhoOne))
  rightReadiness : PaperFactorReadinessList right
  coarseAtomReadiness : PaperFactorAtomReadiness
    (badParentCoarseAtom
      (badParentBufferedIntervalSourceDatum Csource tau rho
        hdeltaTau hTauRho hRhoOne Y)
      (badParentSourceIntervalCover Csource tau rho
        hdeltaTau hTauRho hRhoOne))
  freshReadiness : BadParentFreshBufferedActualHierarchyReadiness
    Csource tau rho hdeltaTau hTauRho hRhoOne Y hrho q
      X.base.selected epsilon hdeltaPos hepsilon

namespace SameSelectedBufferedFreshReadyPaperFactorStep

variable {Csource : CoherentStickyMultiscaleCover source}
  {hdeltaTau : delta <= tau} {hTauRho : tau <= rho}
  {hRhoOne : rho <= 1}
  {Y : Shading
    (Csource.base.cover tau hdeltaTau
      (hTauRho.trans hRhoOne)).coarse.bodyFamily}
  {hrho : 0 < rho}
  {q : {q // q ∈
    (badParentSourceIntervalCover Csource tau rho
      hdeltaTau hTauRho hRhoOne).activeCoarse}}
  {left right : List ActualFactorDatum}
  {lower factorC : ENNReal}
  {X : ParentwiseBadParentMassAwareFactorListState
    (badParentBufferedIntervalSourceDatum Csource tau rho
      hdeltaTau hTauRho hRhoOne Y)
    (badParentSourceIntervalCover Csource tau rho
      hdeltaTau hTauRho hRhoOne)
    left right hrho hRhoOne q lower factorC}
  {epsilon : Real} {hdeltaPos : 0 < delta} {hepsilon : 0 < epsilon}

/-- The unique transition on this literal `q` and `X.base.selected`. -/
def transition
    (step : SameSelectedBufferedFreshReadyPaperFactorStep
      Csource tau rho hdeltaTau hTauRho hRhoOne Y hrho q
        left right lower factorC X epsilon hdeltaPos hepsilon) :=
  parentwiseBadParentPaperFactorTransition_of_bufferedFreshReadiness
    Csource hdeltaPos hepsilon tau rho hdeltaTau hTauRho hRhoOne Y hrho q
    left right lower factorC X step.leftReadiness step.sourceAtomReadiness
    step.rightReadiness step.coarseAtomReadiness step.freshReadiness

end SameSelectedBufferedFreshReadyPaperFactorStep

/-- A finite stage-free trace whose every edge uses the same selected set
carried by its own mass-aware state. -/
inductive SameSelectedBufferedFreshReadyPaperFactorTrace :
    PaperFactorState -> PaperFactorState -> Type 4
  | nil (state : PaperFactorState) :
      SameSelectedBufferedFreshReadyPaperFactorTrace state state
  | cons
      {finalState : PaperFactorState}
      {delta tau rho : NNReal} {sourceIndex : Type}
      [Fintype sourceIndex] [DecidableEq sourceIndex]
      {source : UniformTubeFamily delta sourceIndex}
      {Csource : CoherentStickyMultiscaleCover source}
      {hdeltaTau : delta <= tau} {hTauRho : tau <= rho}
      {hRhoOne : rho <= 1}
      {Y : Shading
        (Csource.base.cover tau hdeltaTau
          (hTauRho.trans hRhoOne)).coarse.bodyFamily}
      {hrho : 0 < rho}
      {q : {q // q ∈
        (badParentSourceIntervalCover Csource tau rho
          hdeltaTau hTauRho hRhoOne).activeCoarse}}
      {left right : List ActualFactorDatum}
      {lower factorC : ENNReal}
      {X : ParentwiseBadParentMassAwareFactorListState
        (badParentBufferedIntervalSourceDatum Csource tau rho
          hdeltaTau hTauRho hRhoOne Y)
        (badParentSourceIntervalCover Csource tau rho
          hdeltaTau hTauRho hRhoOne)
        left right hrho hRhoOne q lower factorC}
      {epsilon : Real} {hdeltaPos : 0 < delta}
      {hepsilon : 0 < epsilon}
      (step : SameSelectedBufferedFreshReadyPaperFactorStep
        Csource tau rho hdeltaTau hTauRho hRhoOne Y hrho q
          left right lower factorC X epsilon hdeltaPos hepsilon)
      (tail : SameSelectedBufferedFreshReadyPaperFactorTrace
        step.transition.successor finalState) :
      SameSelectedBufferedFreshReadyPaperFactorTrace
        step.transition.source finalState

namespace SameSelectedBufferedFreshReadyPaperFactorTrace

/-- Forget readiness objects while retaining every exact product step. -/
def productLedger
    {sourceState finalState : PaperFactorState}
    (trace : SameSelectedBufferedFreshReadyPaperFactorTrace
      sourceState finalState) :
    RepeatedBadParentLedger sourceState.factors finalState.factors := by
  induction trace with
  | nil state => exact .nil state.factors
  | cons step tail ih =>
      exact .cons (paperFactorProductStep step.transition) ih

/-- Literal number of supplied buffered transitions. -/
def transitionCount
    {sourceState finalState : PaperFactorState}
    (trace : SameSelectedBufferedFreshReadyPaperFactorTrace
      sourceState finalState) : Nat :=
  trace.productLedger.stepCount

/-- Retained paper states, including the readiness-aligned source state. -/
def states
    {sourceState finalState : PaperFactorState}
    (trace : SameSelectedBufferedFreshReadyPaperFactorTrace
      sourceState finalState) : List PaperFactorState := by
  induction trace with
  | nil state => exact [state]
  | cons step tail ih => exact step.transition.source :: ih

/-- Exact accumulated radius and two-sided cardinality products for the
supplied stage-free trace. -/
theorem cumulative_exactProductCertificate
    {sourceState finalState : PaperFactorState}
    (trace : SameSelectedBufferedFreshReadyPaperFactorTrace
      sourceState finalState) :
    factorRadiusProduct sourceState.factors =
        (64 / 3 : NNReal) ^ trace.productLedger.steps.length *
          factorRadiusProduct finalState.factors /\
      factorCardProduct finalState.factors <=
        (trace.productLedger.steps.map
          (fun step => step.uniformityLoss)).prod *
            factorCardProduct sourceState.factors /\
      factorCardProduct sourceState.factors <=
        (trace.productLedger.steps.map (fun step =>
          step.uniformityLoss * step.freshRetentionLoss)).prod *
            factorCardProduct finalState.factors := by
  exact trace.productLedger.cumulative_exactProductCertificate

end SameSelectedBufferedFreshReadyPaperFactorTrace

#print axioms badParentBufferedIntervalSourceDatum
#print axioms parentwiseBadParentPaperFactorTransition_of_bufferedFreshReadiness
#print axioms SameSelectedBufferedFreshReadyPaperFactorStep.transition
#print axioms SameSelectedBufferedFreshReadyPaperFactorTrace.productLedger
#print axioms SameSelectedBufferedFreshReadyPaperFactorTrace.transitionCount
#print axioms SameSelectedBufferedFreshReadyPaperFactorTrace.states
#print axioms
  SameSelectedBufferedFreshReadyPaperFactorTrace.cumulative_exactProductCertificate

end
end Family8ParentwiseBadParentBufferedFreshReadyPaperFactorConnectorV1
