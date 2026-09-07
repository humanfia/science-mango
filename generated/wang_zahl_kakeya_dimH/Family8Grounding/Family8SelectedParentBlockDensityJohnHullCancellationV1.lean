import Family8Grounding.Family8SelectedParentBlockDensityLocalCordobaV1
import Family8Grounding.Family8SelectedParentBucketContainerJacobianEnvelopeV3
import Submission.Kakeya.ConvexFactoring.BoxDimensionsMeasure
import Mathlib.Tactic

/-!
# Same-block density cancellation through the literal John hull

The fixed selected-parent container envelope replaces the winning John box
by the ambient bound `2304^3`.  For a local block-density Katz--Tao input this
throws away the denominator which defines that density.  Here the same
objects are kept literal: the `288`-John inner box bounds the certificate-box
volume by `288^3` times the winning-hull volume, and the latter cancels the
denominator in `blockDensity`.

No occurrence, block, side bucket, or affine map is selected in this file.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentBlockDensityJohnHullCancellationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8SelectedParentBucketContainerJacobianEnvelopeV3
open Family8SelectedParentCertifiedPlankCordobaActualJohnContainerV7
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The literal `288`-John certificate box is controlled by the volume of
the very same winning hull.  This is the inner half of the John certificate,
not an ambient support estimate. -/
theorem selectedParent_certificateBox_volume_le_johnFactor_mul_hullVolume
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length) :
    volume
        (selectedParentGreedyBlockJohnFrame S hrho P k).certificate.box.carrier <=
      (288 : ENNReal) ^ 3 *
        volume ((blockAt S.activeCoarseFamily P k).body : Set Space) := by
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  let H := (blockAt S.activeCoarseFamily P k).body
  have hdimensions : HasBoxDimensions 288 J.side H :=
    ⟨J.certificate.one_le, J.certificate.box,
      J.certificate.side_eq, J.certificate.inner_le,
      J.certificate.outer_le⟩
  have hlower := hdimensions.volume_lower_bound
  have hcoefficient :
      (288 : ENNReal) ^ 3 *
          (((((288 : NNReal)⁻¹ : NNReal) : ENNReal) ^ 3)) = 1 := by
    rw [ENNReal.coe_inv (by norm_num : (288 : NNReal) ≠ 0)]
    have hcancel : (288 : ENNReal) * (288 : ENNReal)⁻¹ = 1 :=
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    calc
      (288 : ENNReal) ^ 3 * (288 : ENNReal)⁻¹ ^ 3 =
          ((288 : ENNReal) * (288 : ENNReal)⁻¹) ^ 3 := by ring
      _ = 1 := by rw [hcancel]; norm_num
  rw [FrameBox.volume_carrier, J.certificate.side_eq]
  calc
    (∏ i, (J.side i : ENNReal)) =
        (288 : ENNReal) ^ 3 *
          (((((288 : NNReal)⁻¹ : NNReal) : ENNReal) ^ 3) *
            ∏ i, (J.side i : ENNReal)) := by
      rw [<- mul_assoc, hcoefficient, one_mul]
    _ <= (288 : ENNReal) ^ 3 * volume (H : Set Space) :=
      mul_le_mul' le_rfl hlower

/-- The normalized container retains the same affine Jacobian while its John
box is bounded by the literal winning-hull volume. -/
theorem selectedParentBucketNormalizedJohnContainer_volume_le_jacobian_mul_johnFactor_mul_hullVolume
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int) :
    volume (selectedParentBucketNormalizedJohnContainer
        S hrho P k r label : Set Space) <=
      affineJacobian
          (bucketNormalizedAffineEquiv
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
            label) *
        ((288 : ENNReal) ^ 3 *
          volume ((blockAt S.activeCoarseFamily P k).body : Set Space)) := by
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  have hvolumeEq :=
    volume_bucketNormalizedContainer_eq_jacobian_mul_certificateBox
      J r hr label
  have hbox :=
    selectedParent_certificateBox_volume_le_johnFactor_mul_hullVolume
      S hrho P k
  calc
    volume (selectedParentBucketNormalizedJohnContainer
        S hrho P k r label : Set Space) =
      affineJacobian
          (bucketNormalizedAffineEquiv
            (contractedJohnAffineEquiv J r hr) label) *
        volume J.certificate.box.carrier := by
      simpa only [selectedParentBucketNormalizedJohnContainer, J] using hvolumeEq
    _ <= affineJacobian
          (bucketNormalizedAffineEquiv
            (contractedJohnAffineEquiv J r hr) label) *
        ((288 : ENNReal) ^ 3 *
          volume ((blockAt S.activeCoarseFamily P k).body : Set Space)) :=
      mul_le_mul' le_rfl hbox

/-- On one literal greedy block, its density times its winning-hull volume
is exactly the indexed volume of its selected subtype family. -/
theorem blockDensity_mul_hullVolume_eq_selectedParentBlock_familyVolume
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length) :
    blockDensity S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P k) *
        volume ((blockAt S.activeCoarseFamily P k).body : Set Space) =
      familyVolume
        (selectedCoarseFamily S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P k).fiber) := by
  have hvolume0 :
      volume ((blockAt S.activeCoarseFamily P k).body : Set Space) ≠ 0 := by
    obtain ⟨p, hp⟩ := (blockAt S.activeCoarseFamily P k).fiber_nonempty
    have hcontained := (blockAt S.activeCoarseFamily P k).contained p hp
    have hpVolume : 0 < volume (S.activeCoarseFamily p : Set Space) := by
      change 0 < volume (S.coarse.tubes p.1).carrier
      exact (S.coarse.tubes p.1).volume_pos hrho
    exact (hpVolume.trans_le (measure_mono hcontained)).ne'
  have hvolumeTop :
      volume ((blockAt S.activeCoarseFamily P k).body : Set Space) ≠ ∞ :=
    (blockAt S.activeCoarseFamily P k).body.isCompact.measure_lt_top.ne
  have hdensity :
      blockDensity S.activeCoarseFamily
            (blockAt S.activeCoarseFamily P k) *
          volume ((blockAt S.activeCoarseFamily P k).body : Set Space) =
        blockMass S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P k) := by
    unfold blockDensity
    exact ENNReal.div_mul_cancel hvolume0 hvolumeTop
  have hfamily :
      familyVolume
          (selectedCoarseFamily S.activeCoarseFamily
            (blockAt S.activeCoarseFamily P k).fiber) =
        blockMass S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P k) := by
    rw [selectedCoarseFamily_volume]
    rfl
  exact hdensity.trans hfamily.symm

/-- Exact same-object density cancellation.  The local block-density
Katz--Tao coefficient is absorbed by the literal winning-hull volume before
any fixed ambient envelope is taken. -/
theorem blockDensity_mul_selectedParentBucketNormalizedJohnContainer_volume_le
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int) :
    blockDensity S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P k) *
        volume (selectedParentBucketNormalizedJohnContainer
          S hrho P k r label : Set Space) <=
      affineJacobian
          (bucketNormalizedAffineEquiv
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
            label) *
        ((288 : ENNReal) ^ 3 *
          familyVolume
            (selectedCoarseFamily S.activeCoarseFamily
              (blockAt S.activeCoarseFamily P k).fiber)) := by
  let d := blockDensity S.activeCoarseFamily
    (blockAt S.activeCoarseFamily P k)
  let J : ENNReal := affineJacobian
    (bucketNormalizedAffineEquiv
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      label)
  have hcontainer :=
    selectedParentBucketNormalizedJohnContainer_volume_le_jacobian_mul_johnFactor_mul_hullVolume
      S hrho P k r hr label
  have hdensity :=
    blockDensity_mul_hullVolume_eq_selectedParentBlock_familyVolume
      S hrho P k
  calc
    d * volume (selectedParentBucketNormalizedJohnContainer
        S hrho P k r label : Set Space) <=
      d * (J * ((288 : ENNReal) ^ 3 *
        volume ((blockAt S.activeCoarseFamily P k).body : Set Space))) :=
      mul_le_mul' le_rfl hcontainer
    _ = J * ((288 : ENNReal) ^ 3 *
        (d * volume
          ((blockAt S.activeCoarseFamily P k).body : Set Space))) := by
      ac_rfl
    _ = J * ((288 : ENNReal) ^ 3 *
        familyVolume
          (selectedCoarseFamily S.activeCoarseFamily
            (blockAt S.activeCoarseFamily P k).fiber)) := by
      rw [hdensity]

#print axioms
  selectedParent_certificateBox_volume_le_johnFactor_mul_hullVolume
#print axioms
  selectedParentBucketNormalizedJohnContainer_volume_le_jacobian_mul_johnFactor_mul_hullVolume
#print axioms
  blockDensity_mul_hullVolume_eq_selectedParentBlock_familyVolume
#print axioms
  blockDensity_mul_selectedParentBucketNormalizedJohnContainer_volume_le

end
end Family8SelectedParentBlockDensityJohnHullCancellationV1
