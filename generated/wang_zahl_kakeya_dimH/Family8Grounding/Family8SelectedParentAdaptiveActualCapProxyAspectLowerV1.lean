import Family8Grounding.Family8AdaptiveFullFiberCapProxyAspectLowerV1
import Family8Grounding.Family8SelectedParentCenteredProxyKatzTaoFiniteV1
import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalMassPopularEndpointV3
import Mathlib.Tactic

/-!
# The selected actual bucket cap retains a proxy-aspect reserve
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentAdaptiveActualCapProxyAspectLowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8AdaptiveFullFiberCapProxyAspectLowerV1
open Family8SelectedParentCenteredProxyKatzTaoFiniteV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveThinCountFullFiberOrHullThinV3
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalMassPopularEndpointV3
open Family8SelectedParentPlankCenteredAdaptiveThinCountUniformEq46CountV2
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8SelectedParentPlankCenteredHalfPostKatzTaoV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The canonical cap used by the local mass-popular Eq. (46) producer
retains an actual member's transformed proxy constant and bucket aspect. -/
theorem exists_actualProxy_mul_bucketAspect_sq_le_centeredAdaptiveActualBucketFullFiberNatCap
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (hoccupied : label ∈ occupiedWeightBuckets
      (Finset.univ : Finset
        {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
      (fun p => sideShapeLabel
        (selectedParentLongRelabeledSide
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho p)))
    (hdelta : 0 < delta) (C : ENNReal) (hCfinite : C ≠ ∞) :
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let s := selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r label
    let hplank := selectedParentLiteralPlankBucket_isPlank
      S hrho P k r hr label
    ∃ W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
          s e S B hrho label hplank W C *
          (((bucketShortB label : ENNReal) /
            (bucketShortA label : ENNReal)) ^ (2 : Nat)) <=
        (centeredAdaptiveActualBucketFullFiberNatCap
          S hrho P k r hr label C : ENNReal) := by
  dsimp only
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  obtain ⟨p, _hp, hpLabel⟩ := mem_occupiedWeightBuckets_iff.mp hoccupied
  let W : {p // p ∈ selectedParentPlankBucketIndices
      e S B hrho label} := ⟨p, by
    rw [selectedParentPlankBucketIndices, mem_sideShapeBucket_iff]
    exact ⟨Finset.mem_univ _, hpLabel⟩⟩
  let s := selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r label
  let hplank := selectedParentLiteralPlankBucket_isPlank
    S hrho P k r hr label
  let Cproxy := centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
    s e S B hrho label hplank W C
  have hCproxyfinite : Cproxy ≠ ∞ :=
    centeredHalfPostSelectedPlankFineProxyKatzTaoConstant_ne_top
      s e S B hrho label hplank W hdelta hCfinite
  have hlocal : Cproxy *
        (((bucketShortB label : ENNReal) /
          (bucketShortA label : ENNReal)) ^ (2 : Nat)) <=
      (adaptiveThinCountFullFiberNatCap Cproxy label : ENNReal) :=
    proxy_mul_bucketAspect_sq_le_adaptiveThinCountFullFiberNatCap
      Cproxy hCproxyfinite label
  have huniform : adaptiveThinCountFullFiberNatCap Cproxy label <=
      centeredAdaptiveUniformFullFiberNatCap
        s e S B hrho label hplank C := by
    exact actualFullFiberNatCap_le_centeredAdaptiveUniform
      s e S B hrho label hplank C W
  refine ⟨W, ?_⟩
  exact hlocal.trans (by
    exact_mod_cast huniform)

#print axioms
  exists_actualProxy_mul_bucketAspect_sq_le_centeredAdaptiveActualBucketFullFiberNatCap

end
end Family8SelectedParentAdaptiveActualCapProxyAspectLowerV1
