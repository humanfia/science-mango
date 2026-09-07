import Family8Grounding.Family8QFreshNextActiveReadinessExactDef212V1

/-!
# Final q-fresh next-active readiness wrapper

The wrapper exposes the exact restricted source atom with no extra inputs or
assumptions beyond the destination hierarchy `H` and crossing destination `Y`.
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

/-- The first cross-step readiness seam produced for the exact restricted
q-fresh next-active atom. -/
def qFreshNextActiveReadiness
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H) :
    PaperFactorAtomReadiness (qFreshNextActiveSourceAtom Y) where
  admissible := qFreshNextActiveSourceDatum_isAdmissible Y
  coherentCover := qFreshNextActiveCoherentCover H Y
  def212Constant := H.readiness.qFreshK
  exactDef212 := qFreshNextActiveExactDef212 H Y

end
end Family8QFreshNextActiveReadinessProducerV1
