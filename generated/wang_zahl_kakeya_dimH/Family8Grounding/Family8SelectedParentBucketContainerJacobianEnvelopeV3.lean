import Family8Grounding.Family8SelectedParentCertifiedPlankCordobaActualJohnContainerV7
import Family8Grounding.Family8SelectedParentJohnPlankQuantitativeLossV9
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentBucketContainerJacobianEnvelopeV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaActualJohnContainerV7
open Family8SelectedParentJohnBoxAffineTransportV16
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Cancelling the selected-parent normalized container against its Jacobian

V1 and V2 were unbuilt namespace drafts and are intentionally not imported.
The bucket-normalized common John container is the literal image of the
winning-hull certificate box under the same affine equivalence used in the
source-mass transport.  Unit-ball support bounds every original side by
2304, leaving a fixed residual volume ratio.
-/

theorem bucketNormalized_image_certificateBox
    {H : ConvexBody Space} (J : PositiveJohnFrame H)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int) :
    bucketNormalizedAffineEquiv (contractedJohnAffineEquiv J r hr) label ''
        J.certificate.box.carrier =
      (normalizedJohnBox J ((sideShapeUpper label 2)⁻¹ * r)).carrier := by
  let dr := scalarDilationAffineEquiv r hr
  let t := (sideShapeUpper label 2)⁻¹
  have ht : 0 < t := inv_pos.mpr (sideShapeUpper_pos label 2)
  let dt := scalarDilationAffineEquiv t ht
  have hrescale : J.certificate.box.rescale 1 = J.certificate.box := by
    simp [FrameBox.rescale]
  have hJ := image_rescaledBox_eq_normalizedJohnBox J 1
  rw [hrescale] at hJ
  have hrImage := scalarDilation_image_normalizedJohnBox J r hr 1
  have htImage := scalarDilation_image_normalizedJohnBox J t ht r
  simp only [mul_one] at hrImage
  rw [← htImage, ← hrImage, ← hJ]
  change (J.affineEquiv.trans dr).trans dt '' J.certificate.box.carrier =
    dt '' (dr '' (J.affineEquiv '' J.certificate.box.carrier))
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨dr (J.affineEquiv x),
      ⟨J.affineEquiv x, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨_z, ⟨_w, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem volume_bucketNormalizedContainer_eq_jacobian_mul_certificateBox
    {H : ConvexBody Space} (J : PositiveJohnFrame H)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int) :
    volume
        ((normalizedJohnBox J ((sideShapeUpper label 2)⁻¹ * r)).body :
          Set Space) =
      affineJacobian
          (bucketNormalizedAffineEquiv
            (contractedJohnAffineEquiv J r hr) label) *
        volume J.certificate.box.carrier := by
  rw [FrameBox.coe_body]
  rw [← bucketNormalized_image_certificateBox J r hr label]
  exact volume_image_affineEquiv _ _

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem selectedParent_certificateBox_volume_le_fixed
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length) :
    volume
        (selectedParentGreedyBlockJohnFrame S hrho P k).certificate.box.carrier ≤
      (2304 : ENNReal) ^ 3 := by
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  have hside : ∀ i,
      (J.certificate.box.side i : ENNReal) ≤ 2304 := by
    intro i
    rw [J.certificate.side_eq]
    exact_mod_cast selectedParentGreedyBlockJohnSide_le_2304
      hfineContained S hrho hrhoOne P k i
  rw [FrameBox.volume_carrier, Fin.prod_univ_three]
  calc
    (J.certificate.box.side 0 : ENNReal) *
          (J.certificate.box.side 1 : ENNReal) *
          (J.certificate.box.side 2 : ENNReal) ≤
        2304 * 2304 * 2304 := by
      exact mul_le_mul' (mul_le_mul' (hside 0) (hside 1)) (hside 2)
    _ = (2304 : ENNReal) ^ 3 := by ring

theorem selectedParentBucketNormalizedJohnContainer_volume_le_jacobian_fixed
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int) :
    volume (selectedParentBucketNormalizedJohnContainer
        S hrho P k r label : Set Space) ≤
      affineJacobian
          (bucketNormalizedAffineEquiv
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
            label) * (2304 : ENNReal) ^ 3 := by
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  have hvolumeEq :=
    volume_bucketNormalizedContainer_eq_jacobian_mul_certificateBox
      J r hr label
  have hbox := selectedParent_certificateBox_volume_le_fixed
    hfineContained S hrho hrhoOne P k
  calc
    volume (selectedParentBucketNormalizedJohnContainer
        S hrho P k r label : Set Space) =
      affineJacobian
          (bucketNormalizedAffineEquiv
            (contractedJohnAffineEquiv J r hr) label) *
        volume J.certificate.box.carrier := by
      simpa only [selectedParentBucketNormalizedJohnContainer, J] using hvolumeEq
    _ ≤ affineJacobian
          (bucketNormalizedAffineEquiv
            (contractedJohnAffineEquiv J r hr) label) *
        (2304 : ENNReal) ^ 3 := mul_le_mul' le_rfl hbox

#print axioms bucketNormalized_image_certificateBox
#print axioms volume_bucketNormalizedContainer_eq_jacobian_mul_certificateBox
#print axioms selectedParent_certificateBox_volume_le_fixed
#print axioms
  selectedParentBucketNormalizedJohnContainer_volume_le_jacobian_fixed

end
end Family8SelectedParentBucketContainerJacobianEnvelopeV3
