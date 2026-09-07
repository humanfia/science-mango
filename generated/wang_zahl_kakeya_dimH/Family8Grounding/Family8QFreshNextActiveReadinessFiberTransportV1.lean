import Family8Grounding.Family8QFreshNextActiveReadinessScaleReindexV1
import Mathlib.Tactic

/-!
# Fibre transport for the q-fresh next-active scale cover
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8QFreshNextActiveReadinessProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8DoublyBufferedDef212GroundedOneStepRunV1
open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperFactorStateV1
open Family8ParentwiseBadParentDualChildOrchestrationCertificateV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseCrossingIntegratedSuccessorV1
open Family8QFreshNextActiveFinePaperStateTransportV1
open Family8SelectedFiberDoublyBufferedPaperFactorConnectorV1
open Family8SelectedFiberFaithfulBufferedCoherentSuccessorV2
open Family8SourceDef212BoundCrossingTransitionV2
open Family8SourceDef212BoundCrossingTransitionV2.SourceDef212CrossingIntegratedSuccessor
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta tau : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  {source : UniformTubeFamily delta sourceIndex}
  {depth : Nat}
  {Csource : CoherentStickyMultiscaleCover source}
  {hdeltaTau : delta ≤ tau} {hTauOne : tau ≤ 1}
  {Ysource : Shading
    (Csource.base.cover tau hdeltaTau hTauOne).coarse.bodyFamily}
  {hDtau : (rerootedPaperSourceDatum Csource tau hdeltaTau
    hTauOne Ysource).IsAdmissible}
  {S : FiniteScaleSequence tau depth}
  {epsilon : Real} {hepsilon : 0 ≤ epsilon}
  {eta : Nat → Real} {N : Nat}
  {W : FirstParentwiseNormalizedCrossingWitness
    (rerootedPaperSourceDatum Csource tau hdeltaTau hTauOne Ysource)
    hDtau (rerootedPaperSourceCover Csource tau hdeltaTau hTauOne)
    S epsilon hepsilon eta N}
  {R : SourceDef212CrossingSuccessorReadiness W}
  {X : SourceDef212CrossingIntegratedSuccessor W R}

noncomputable def qFreshNextActiveFiberEquiv
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1)
    (k : Fin (qFreshFullScaleCover H rho hChildRho hRhoOne).coarseCard) :
    {i // i ∈ (qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne).fiber k} ≃
      {j // j ∈ (qFreshFullScaleCover H rho hChildRho hRhoOne).fiber k} :=
  Family8StickyScaleCoverFineEquivReindexV1.StickyScaleCover.reindexFineOfActiveUnivFiberEquiv
      (qFreshFullScaleCover H rho hChildRho hRhoOne)
      (qFreshNextActiveSourceDatum Y).family
      (qFreshNextActiveHierarchyIndexEquiv H Y)
      (qFreshNextActiveHierarchyIndexEquiv_tube H Y)
      (qFreshFullScaleCover_activeFine_eq_univ H rho hChildRho hRhoOne)
      (by rfl) k

@[simp] theorem qFreshNextActiveFiberEquiv_body
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1)
    (k : Fin (qFreshFullScaleCover H rho hChildRho hRhoOne).coarseCard)
    (i : {i // i ∈
      (qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne).fiber k}) :
    (qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne).fiberFamily k i =
      (qFreshFullScaleCover H rho hChildRho hRhoOne).fiberFamily k
        (qFreshNextActiveFiberEquiv H Y rho hChildRho hRhoOne k i) :=
  rfl

/-
theorem qFreshNextActive_fiber_card_eq
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1)
    (k : Fin (qFreshFullScaleCover H rho hChildRho hRhoOne).coarseCard) :
    ((qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne).fiber k).card =
      ((qFreshFullScaleCover H rho hChildRho hRhoOne).fiber k).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_congr
      (qFreshNextActiveFiberEquiv H Y rho hChildRho hRhoOne k)

theorem qFreshNextActive_isCUniform
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1) :
    IsCUniform (qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne)
      (H.readiness.qFreshK : ENNReal) := by
  intro k hk l hl
  rw [qFreshNextActive_fiber_card_eq H Y rho hChildRho hRhoOne k,
    qFreshNextActive_fiber_card_eq H Y rho hChildRho hRhoOne l]
  exact H.readiness.qFreshExact.c_uniform rho hChildRho hRhoOne
    k hk l hl

-/
#print axioms qFreshNextActiveFiberEquiv
#print axioms qFreshNextActiveFiberEquiv_body

end
end Family8QFreshNextActiveReadinessProducerV1
