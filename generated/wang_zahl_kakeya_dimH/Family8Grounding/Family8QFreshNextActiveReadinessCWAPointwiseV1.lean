import Family8Grounding.Family8QFreshNextActiveReadinessGeometryCWAV1
import Family8Grounding.Family8ConvexWolffPointwiseReindexV1

/-!
# Lightweight CWA transport for q-fresh next-active readiness

The concrete normalized-fibre equality is discharged pointwise and never
exported as a standalone theorem with a very large instantiated type.
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
open Family8ConvexWolffPointwiseReindexV1
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

theorem qFreshNextActive_rescaledFibres_cwa_pointwise
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1) :
    (qFreshNextActiveUnitRescalingGeometry
      H Y rho hChildRho hRhoOne).FibresSatisfyCWA
        (H.readiness.qFreshK : ENNReal) := by
  intro k
  refine satisfiesConvexWolffAxioms_equiv_of_pointwise_eq
    (F := UnitRescalingGeometry.rescaledFiberFamily
      (H.readiness.qFreshExact.unitRescalingGeometry
        rho hChildRho hRhoOne)
      (qFreshNextActiveOldParent H Y rho hChildRho hRhoOne k))
    (G := UnitRescalingGeometry.rescaledFiberFamily
      (qFreshNextActiveUnitRescalingGeometry
        H Y rho hChildRho hRhoOne) k)
    (qFreshNextActiveFiberEquiv H Y rho hChildRho hRhoOne k.1) ?_ ?_
  · intro i
    rfl
  · exact H.readiness.qFreshExact.rescaled_fibres_cwa
      rho hChildRho hRhoOne
        (qFreshNextActiveOldParent H Y rho hChildRho hRhoOne k)

#print axioms qFreshNextActive_rescaledFibres_cwa_pointwise

end
end Family8QFreshNextActiveReadinessProducerV1
