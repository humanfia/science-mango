import Family8Grounding.Family8QFreshNextActiveReadinessCoherentCoverV1
import Family8Grounding.Family8QFreshNextActiveReadinessFiberUniformV1
import Family8Grounding.Family8QFreshNextActiveReadinessPartitioningV1
import Family8Grounding.Family8QFreshNextActiveReadinessGeometryCWAV1
import Family8Grounding.Family8QFreshNextActiveReadinessCWAPointwiseV1

/-!
# Exact Definition 2.12 package for the q-fresh next-active cover

This layer only packages the already transported finite, geometric, and
pointwise CWA facts for the coherent cover assembled upstream.
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

def qFreshNextActiveExactDef212
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H) :
    ExactScaleDef212Inputs
      (qFreshNextActiveCoherentCover H Y).base
      H.readiness.qFreshK where
  delta_pos := H.readiness.qFreshExact.delta_pos
  one_lt_C := H.readiness.qFreshExact.one_lt_C
  fine_refined_eq_univ := rfl
  fine_pairwise_paperEssentiallyDistinct :=
    qFreshNextActive_pairwise_paperEssentiallyDistinct H Y
  c_uniform := fun rho hChildRho hRhoOne ↦
    qFreshNextActive_isCUniform H Y rho hChildRho hRhoOne
  doubled_parent_partitioning := fun rho hChildRho hRhoOne ↦
    qFreshNextActive_isDoubledParentPartitioning
      H Y rho hChildRho hRhoOne
  unitRescalingGeometry := fun rho hChildRho hRhoOne ↦
    qFreshNextActiveUnitRescalingGeometry
      H Y rho hChildRho hRhoOne
  rescaled_fibres_cwa := fun rho hChildRho hRhoOne ↦
    qFreshNextActive_rescaledFibres_cwa_pointwise
      H Y rho hChildRho hRhoOne

end
end Family8QFreshNextActiveReadinessProducerV1
