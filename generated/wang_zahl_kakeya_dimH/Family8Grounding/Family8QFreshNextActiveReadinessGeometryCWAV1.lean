import Family8Grounding.Family8QFreshNextActiveReadinessPartitioningV1
import Mathlib.Tactic

/-!
# Geometry and CWA transport for q-fresh next-active readiness

Only one occupied parent is converted at a time.  Its John witness and
normalization are reused literally; the normalized fibre is reindexed by the
already exact finite fibre equivalence.
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

/-- The corresponding occupied parent of the genuine q-fresh cover. -/
def qFreshNextActiveOldParent
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1)
    (k : {k // k ∈
      (qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne).activeCoarse}) :
    {k // k ∈
      (qFreshFullScaleCover H rho hChildRho hRhoOne).activeCoarse} :=
  ⟨k.1, k.2⟩

/-- Reuse the literal source John witness and affine normalization at each
occupied target parent. -/
noncomputable def qFreshNextActiveUnitRescalingGeometry
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1) :
    UnitRescalingGeometry
      (qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne) := by
  let Old := H.readiness.qFreshExact.unitRescalingGeometry
    rho hChildRho hRhoOne
  exact
    { johnWitness := fun k =>
        Old.johnWitness
          (qFreshNextActiveOldParent H Y rho hChildRho hRhoOne k)
      unitRescaling := fun k =>
        Old.unitRescaling
          (qFreshNextActiveOldParent H Y rho hChildRho hRhoOne k)
      johnOuter_image_eq_unitBall := fun k =>
        Old.johnOuter_image_eq_unitBall
          (qFreshNextActiveOldParent H Y rho hChildRho hRhoOne k) }

/-
/-- The target normalized fibre is the source normalized fibre under the
exact finite reindexing. -/
theorem qFreshNextActive_rescaledFiberFamily_eq_reindex
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1)
    (k : {k // k ∈
      (qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne).activeCoarse}) :
    UnitRescalingGeometry.rescaledFiberFamily
        (qFreshNextActiveUnitRescalingGeometry
          H Y rho hChildRho hRhoOne) k =
      reindexConvexFamily
        (qFreshNextActiveFiberEquiv H Y rho hChildRho hRhoOne k.1)
        (UnitRescalingGeometry.rescaledFiberFamily
          (H.readiness.qFreshExact.unitRescalingGeometry
            rho hChildRho hRhoOne)
          (qFreshNextActiveOldParent H Y rho hChildRho hRhoOne k)) := by
  funext i
  rfl

theorem qFreshNextActive_rescaledFibres_cwa
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
  let targetFamily := UnitRescalingGeometry.rescaledFiberFamily
    (qFreshNextActiveUnitRescalingGeometry H Y rho hChildRho hRhoOne) k
  let sourceFamily := UnitRescalingGeometry.rescaledFiberFamily
    (H.readiness.qFreshExact.unitRescalingGeometry rho hChildRho hRhoOne)
    (qFreshNextActiveOldParent H Y rho hChildRho hRhoOne k)
  let e := qFreshNextActiveFiberEquiv H Y rho hChildRho hRhoOne k.1
  have hfamily : targetFamily = reindexConvexFamily e sourceFamily :=
    qFreshNextActive_rescaledFiberFamily_eq_reindex
      H Y rho hChildRho hRhoOne k
  have hreindex : SatisfiesConvexWolffAxioms
      (H.readiness.qFreshK : ENNReal)
      (reindexConvexFamily e sourceFamily) :=
    satisfiesConvexWolffAxioms_reindex e
      (H.readiness.qFreshExact.rescaled_fibres_cwa
        rho hChildRho hRhoOne
          (qFreshNextActiveOldParent H Y rho hChildRho hRhoOne k))
  exact Eq.mpr
    (congrArg (SatisfiesConvexWolffAxioms
      (H.readiness.qFreshK : ENNReal)) hfamily) hreindex

-/
#print axioms qFreshNextActiveOldParent
#print axioms qFreshNextActiveUnitRescalingGeometry

end
end Family8QFreshNextActiveReadinessProducerV1
