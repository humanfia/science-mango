import Family8Grounding.Family8SelectedParentAdaptiveActualCapProxyAspectLowerV1
import Family8Grounding.Family8SelectedParentCenteredProxyKatzTaoLowerV1
import Mathlib.Tactic

/-!
# The selected actual adaptive cap retains the source KT constant and aspect

The actual member supplied by the occupied bucket already retains its proxy
constant times the squared bucket aspect.  At the adaptive radius, the real
source-to-proxy geometric loss is at least one, so the same cap also retains
the source Katz--Tao constant itself.  The only scale input is the packing
smallness already required by the adaptive thin-count branch.
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentAdaptiveActualCapSourceAspectLowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8SelectedParentAdaptiveActualCapProxyAspectLowerV1
open Family8SelectedParentCenteredProxyKatzTaoLowerV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalMassPopularEndpointV3
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8SelectedParentPlankCenteredHalfPostKatzTaoV1
open Family8SelectedParentPlankCenteredHalfPostStructuredRadiusV1
open Family8SelectedParentPlankFineProxyCarrierV3
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

theorem exists_sourceKatzTaoConstant_mul_bucketAspect_sq_le_centeredAdaptiveActualBucketFullFiberNatCap
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
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hsmallPacking : selectedParentCenteredHalfPostAdaptiveProxyScale
      delta rho r label / 8 <= (1 / 100 : NNReal))
    (C : ENNReal) (hCfinite : C ≠ ∞) :
    C * (((bucketShortB label : ENNReal) /
      (bucketShortA label : ENNReal)) ^ (2 : Nat)) <=
      (centeredAdaptiveActualBucketFullFiberNatCap
        S hrho P k r hr label C : ENNReal) := by
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let s := selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r label
  let hplank := selectedParentLiteralPlankBucket_isPlank
    S hrho P k r hr label
  obtain ⟨W, hproxyCap⟩ :=
    exists_actualProxy_mul_bucketAspect_sq_le_centeredAdaptiveActualBucketFullFiberNatCap
      S hrho P k r hr label hoccupied hdelta C hCfinite
  have hsHalf : s <= (2 : NNReal)⁻¹ := by
    have hsTimes : s <= (1 / 100 : NNReal) * 8 := by
      exact (div_le_iff₀ (by norm_num : (0 : NNReal) < 8)).mp
        (by simpa only [s] using hsmallPacking)
    rw [div_mul_eq_mul_div, one_mul] at hsTimes
    have hnum : (8 : NNReal) / 100 <= 1 / 2 := by
      apply (div_le_div_iff₀ (by norm_num) (by norm_num)).2
      norm_num
    simpa only [inv_eq_one_div] using hsTimes.trans hnum
  let hscalar := selectedParent_centeredHalfPost_adaptive_radius_scalar
    (delta := delta) hrho r label
  let hradius := selectedParent_centeredHalfPost_radius_budget
    S hrho P k r hr label B hplank W s hscalar
  have hsourceProxy :
      C <= centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
        s e S B hrho label hplank W C :=
    sourceKatzTaoConstant_le_centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
      s e S B hrho label hplank W hradius hdelta hdeltaHalf hsHalf C
  calc
    C * (((bucketShortB label : ENNReal) /
          (bucketShortA label : ENNReal)) ^ (2 : Nat)) <=
        centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
          s e S B hrho label hplank W C *
            (((bucketShortB label : ENNReal) /
              (bucketShortA label : ENNReal)) ^ (2 : Nat)) := by
      gcongr
    _ <= (centeredAdaptiveActualBucketFullFiberNatCap
          S hrho P k r hr label C : ENNReal) := by
      simpa only [s, e, B, hplank] using hproxyCap

#print axioms
  exists_sourceKatzTaoConstant_mul_bucketAspect_sq_le_centeredAdaptiveActualBucketFullFiberNatCap

end
end Family8SelectedParentAdaptiveActualCapSourceAspectLowerV1
