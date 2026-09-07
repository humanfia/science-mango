import Family8Grounding.Family8QFreshNextActiveReadinessScaleReindexV1

/-!
# Coherent q-fresh next-active cover

This thin layer assembles the reindexed scale covers into the genuine
multiscale hierarchy.  The parent maps and their laws remain the literal
ones owned by the source q-fresh coherent cover.
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

def qFreshNextActiveMultiscaleCover
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H) :
    StickyMultiscaleCover (qFreshNextActiveSourceDatum Y).family where
  cover := fun rho hChildRho hRhoOne ↦
    qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne

def qFreshNextActiveCoherentCover
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H) :
    CoherentStickyMultiscaleCover (qFreshNextActiveSourceDatum Y).family where
  base := qFreshNextActiveMultiscaleCover H Y
  parent := fun r s hChildR hRS hSOne ↦
    H.readiness.qFreshCover.parent r s hChildR hRS hSOne
  parent_mem := by
    intro r s hChildR hRS hSOne k hk
    exact H.readiness.qFreshCover.parent_mem
      r s hChildR hRS hSOne k hk
  parent_surjective := by
    intro r s hChildR hRS hSOne k hk
    exact H.readiness.qFreshCover.parent_surjective
      r s hChildR hRS hSOne k hk
  carrier_subset := by
    intro r s hChildR hRS hSOne k hk
    exact H.readiness.qFreshCover.carrier_subset
      r s hChildR hRS hSOne k hk

end
end Family8QFreshNextActiveReadinessProducerV1
