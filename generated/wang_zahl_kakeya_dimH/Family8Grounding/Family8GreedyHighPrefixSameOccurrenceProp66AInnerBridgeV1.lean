import Family8Grounding.Family8GreedyHighPrefixSameOccurrenceCarrierFloorCancellationV1
import Family8Grounding.Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
import Family8Grounding.Family8SelectedParentBucketContainerJacobianEnvelopeV3
import Family8Grounding.Family8SelectedParentArbitraryBlockPlankBucketV4
import Family8Grounding.Family8Prop66AOuterInnerProductAlgebraV1
import Mathlib.Tactic

/-!
# Same-occurrence carrier cancellation to the Prop. 6.6(A) inner factor

This file changes no selected object.  The source, greedy block, side label,
and arbitrary-block shading have already been fixed.  First, the literal
normalized long-scale cube left after carrier-floor cancellation is bounded
by the Jacobian of the *same* bucket normalization and the genuine fixed John
box volume envelope.  Second, this is composed with the pure carrier-floor
cancellation.

The exact remaining analytic input is displayed explicitly: the fixed
Katz--Tao/angle coefficient must fit inside the requested Prop. 6.6(A) inner
factor.  No multiplicity conclusion, exact assembly, or reselection is used.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8GreedyHighPrefixSameOccurrenceProp66AInnerBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8GreedyHighPrefixSameOccurrenceCarrierFloorCancellationV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentArbitraryBlockPlankBucketV4
open Family8SelectedParentBucketContainerJacobianEnvelopeV3
open Family8SelectedParentCertifiedPlankCordobaActualJohnContainerV7
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The normalized long-scale cube of one literal selected-parent bucket is
bounded by the Jacobian of that same bucket map and the fixed John-box
volume.  The thresholded angle constant is retained literally. -/
theorem thresholdedCordobaNumerator_le_sameBucketJacobian_fixed
    (hfineContained : forall i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int) :
    certifiedPlankThresholdedAngleScaleCap 576 *
        (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3)) <=
      affineJacobian
          (bucketNormalizedAffineEquiv
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
            label) *
        (certifiedPlankThresholdedAngleScaleCap 576 *
          (2304 : ENNReal) ^ 3) := by
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let J : ENNReal := affineJacobian (bucketNormalizedAffineEquiv e label)
  let t : NNReal := (sideShapeUpper label 2)⁻¹ * r
  have hcontainer :=
    selectedParentBucketNormalizedJohnContainer_volume_le_jacobian_fixed
      hfineContained S hrho hrhoOne P k r hr label
  have ht : ((t : NNReal) : ENNReal) ^ 3 <= J * (2304 : ENNReal) ^ 3 := by
    rw [volume_selectedParentBucketNormalizedJohnContainer] at hcontainer
    simpa only [t, J, e] using hcontainer
  calc
    certifiedPlankThresholdedAngleScaleCap 576 *
        (((t : NNReal) : ENNReal) ^ 3) <=
      certifiedPlankThresholdedAngleScaleCap 576 *
        (J * (2304 : ENNReal) ^ 3) := mul_le_mul' le_rfl ht
    _ = J * (certifiedPlankThresholdedAngleScaleCap 576 *
        (2304 : ENNReal) ^ 3) := by ac_rfl

/-- Exact same-object handoff after carrier-floor cancellation.  Its sole
new premise is the literal residual comparison, with the actual normalized
long-scale cube and the actual Jacobian still present.  Thus the theorem
does not strengthen the consumer to a global or fixed-envelope assertion. -/
theorem sourceDensity_mul_thresholdedCordobaScale_le_prop66AInner_of_exactResidual
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (sourceDensity loss KT sourcePower : ENNReal)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (Z : Shading (selectedCoarseFamily S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k).fiber))
    (tubesPerPlank : Nat) (epsilon beta : Real)
    (hfloor :
      let B := (blockAt S.activeCoarseFamily P k).fiber
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
      let Ybucket := selectedParentArbitraryPlankBucketShading
        e S B hrho label Z
      affineJacobian (bucketNormalizedAffineEquiv e label) *
          (sourceDensity * ((rho : ENNReal) ^ 2 / 2)) <=
        loss * quantitativeCarrierFloor Ybucket)
    (hresidual :
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
      KT * (certifiedPlankThresholdedAngleScaleCap 576 *
          ((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3)) <=
        affineJacobian (bucketNormalizedAffineEquiv e label) *
          (sourcePower * proposition66AInnerFactor rho
            (bucketShortA label) (bucketShortB label)
            tubesPerPlank epsilon beta)) :
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let Ybucket := selectedParentArbitraryPlankBucketShading
      e S B hrho label Z
    (affineJacobian (bucketNormalizedAffineEquiv e label) *
        (sourceDensity * ((rho : ENNReal) ^ 2 / 2))) *
        (KT * (certifiedPlankThresholdedAngleScaleCap 576 *
          (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
            quantitativeCarrierFloor Ybucket))) <=
      loss *
        (affineJacobian (bucketNormalizedAffineEquiv e label) *
          (sourcePower * proposition66AInnerFactor rho
            (bucketShortA label) (bucketShortB label)
            tubesPerPlank epsilon beta)) := by
  dsimp only at hfloor hresidual ⊢
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let Ybucket := selectedParentArbitraryPlankBucketShading
    e S B hrho label Z
  have hcancel :=
    quantitativeCarrierFloorDensity_mul_thresholdedCordobaScale_le
      Ybucket
      (affineJacobian (bucketNormalizedAffineEquiv e label))
      sourceDensity loss KT rho r (sideShapeUpper label 2) hfloor
  calc
    (affineJacobian (bucketNormalizedAffineEquiv e label) *
        (sourceDensity * ((rho : ENNReal) ^ 2 / 2))) *
        (KT * (certifiedPlankThresholdedAngleScaleCap 576 *
          (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
            quantitativeCarrierFloor Ybucket))) <=
      loss * (KT * (certifiedPlankThresholdedAngleScaleCap 576 *
        ((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3))) :=
          hcancel
    _ <= loss *
        (affineJacobian (bucketNormalizedAffineEquiv e label) *
          (sourcePower * proposition66AInnerFactor rho
            (bucketShortA label) (bucketShortB label)
            tubesPerPlank epsilon beta)) := mul_le_mul' le_rfl hresidual

/-- A convenient sufficient condition for the exact residual.  The selected
bucket geometry automatically removes its Jacobian and long-scale cube,
leaving only the fixed Katz--Tao/angle coefficient versus the requested
inner factor.  This condition is intentionally separate from the exact
consumer above, so callers need not assume it when a sharper local estimate
is available. -/
theorem sourceDensity_mul_thresholdedCordobaScale_le_prop66AInner_of_fixedResidual
    (hfineContained : forall i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (sourceDensity loss KT sourcePower : ENNReal)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (Z : Shading (selectedCoarseFamily S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k).fiber))
    (tubesPerPlank : Nat) (epsilon beta : Real)
    (hfloor :
      let B := (blockAt S.activeCoarseFamily P k).fiber
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
      let Ybucket := selectedParentArbitraryPlankBucketShading
        e S B hrho label Z
      affineJacobian (bucketNormalizedAffineEquiv e label) *
          (sourceDensity * ((rho : ENNReal) ^ 2 / 2)) <=
        loss * quantitativeCarrierFloor Ybucket)
    (hfixed :
      KT * (certifiedPlankThresholdedAngleScaleCap 576 *
          (2304 : ENNReal) ^ 3) <=
        sourcePower * proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          tubesPerPlank epsilon beta) :
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let Ybucket := selectedParentArbitraryPlankBucketShading
      e S B hrho label Z
    (affineJacobian (bucketNormalizedAffineEquiv e label) *
        (sourceDensity * ((rho : ENNReal) ^ 2 / 2))) *
        (KT * (certifiedPlankThresholdedAngleScaleCap 576 *
          (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
            quantitativeCarrierFloor Ybucket))) <=
      loss *
        (affineJacobian (bucketNormalizedAffineEquiv e label) *
          (sourcePower * proposition66AInnerFactor rho
            (bucketShortA label) (bucketShortB label)
            tubesPerPlank epsilon beta)) := by
  apply sourceDensity_mul_thresholdedCordobaScale_le_prop66AInner_of_exactResidual
    S hrho P k sourceDensity loss KT sourcePower r hr label Z
      tubesPerPlank epsilon beta hfloor
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  have hgeometry := thresholdedCordobaNumerator_le_sameBucketJacobian_fixed
    hfineContained S hrho hrhoOne P k r hr label
  calc
    KT * (certifiedPlankThresholdedAngleScaleCap 576 *
        ((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3)) <=
      KT * (affineJacobian (bucketNormalizedAffineEquiv e label) *
        (certifiedPlankThresholdedAngleScaleCap 576 *
          (2304 : ENNReal) ^ 3)) := mul_le_mul' le_rfl hgeometry
    _ = affineJacobian (bucketNormalizedAffineEquiv e label) *
        (KT * (certifiedPlankThresholdedAngleScaleCap 576 *
          (2304 : ENNReal) ^ 3)) := by ac_rfl
    _ <= affineJacobian (bucketNormalizedAffineEquiv e label) *
        (sourcePower * proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          tubesPerPlank epsilon beta) := mul_le_mul' le_rfl hfixed

#print axioms thresholdedCordobaNumerator_le_sameBucketJacobian_fixed
#print axioms
  sourceDensity_mul_thresholdedCordobaScale_le_prop66AInner_of_exactResidual
#print axioms
  sourceDensity_mul_thresholdedCordobaScale_le_prop66AInner_of_fixedResidual

end
end Family8GreedyHighPrefixSameOccurrenceProp66AInnerBridgeV1
