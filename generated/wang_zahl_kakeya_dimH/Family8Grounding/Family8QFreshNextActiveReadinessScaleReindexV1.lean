import Family8Grounding.Family8QFreshNextActiveHierarchyIndexEquivV1
import Family8Grounding.Family8StickyScaleCoverFineEquivReindexV1
import Mathlib.Tactic

/-!
# One q-fresh next-active scale cover

This thin module instantiates the exact generic fine-index reindexing with
the canonical q-fresh active-subtype equivalence already proved upstream.
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

/-- Reindex only the fine side of one genuine q-fresh scale cover. -/
noncomputable def qFreshNextActiveScaleCover
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1) :
    StickyScaleCover (qFreshNextActiveSourceDatum Y).family rho :=
  Family8StickyScaleCoverFineEquivReindexV1.StickyScaleCover.reindexFineOfActiveUniv
    (qFreshFullScaleCover H rho hChildRho hRhoOne)
    (qFreshNextActiveSourceDatum Y).family
    (qFreshNextActiveHierarchyIndexEquiv H Y)
    (qFreshNextActiveHierarchyIndexEquiv_tube H Y)
    (qFreshFullScaleCover_activeFine_eq_univ H rho hChildRho hRhoOne)
    (by rfl)

@[simp] theorem qFreshNextActiveScaleCover_coarse
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1) :
    (qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne).coarse =
      (qFreshFullScaleCover H rho hChildRho hRhoOne).coarse :=
  rfl

@[simp] theorem qFreshNextActiveScaleCover_activeCoarse
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1) :
    (qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne).activeCoarse =
      (qFreshFullScaleCover H rho hChildRho hRhoOne).activeCoarse :=
  rfl

#print axioms qFreshNextActiveScaleCover
#print axioms qFreshNextActiveScaleCover_coarse
#print axioms qFreshNextActiveScaleCover_activeCoarse

end
end Family8QFreshNextActiveReadinessProducerV1
