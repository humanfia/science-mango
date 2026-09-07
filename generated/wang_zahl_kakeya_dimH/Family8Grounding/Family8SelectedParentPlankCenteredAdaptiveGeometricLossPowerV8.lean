import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV2
import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV7

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV8

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8ContractedJohnActualTubeProxyV1
open Family8SelectedParentBucketContainerJacobianEnvelopeV3
open Family8SelectedParentCertifiedPlankCordobaActualJohnContainerV7
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV2
open Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV7
open Family8SelectedParentPlankCenteredHalfPostCarrierV1
open Family8SelectedParentPlankHalfPostKatzTaoV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem one_div_3456_le_selectedParent_bucketScale
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label}) :
    (1 / 3456 : NNReal) <= (sideShapeUpper label 2)⁻¹ * r := by
  have hu := selectedParent_sideShapeUpper_two_le_3456_mul_r
    S hrho P k r hr label W
  have huPos : 0 < sideShapeUpper label 2 := sideShapeUpper_pos label 2
  rw [show (sideShapeUpper label 2)⁻¹ * r =
    r / sideShapeUpper label 2 by simp [div_eq_mul_inv, mul_comm]]
  apply (div_le_div_iff₀ (by norm_num : (0 : NNReal) < 3456) huPos).2
  simpa [mul_comm] using hu

/-- The actual selected bucket supplies a fixed inverse-Jacobian bound for
the centered map. -/
theorem one_le_centeredAdaptiveJacobianInverseConstant_mul_affineJacobian
    (hfineContained : forall i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (hplank : forall W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label}) :
    1 <= centeredAdaptiveJacobianInverseConstant *
      affineJacobian
        (centeredHalfPostBucketAffineEquiv
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho label hplank W) := by
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let JB : ENNReal := affineJacobian (bucketNormalizedAffineEquiv e label)
  let JC : ENNReal := affineJacobian
    (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W)
  let t : NNReal := (sideShapeUpper label 2)⁻¹ * r
  have ht : (1 / 3456 : NNReal) <= t := by
    simpa only [t, e, B] using
      one_div_3456_le_selectedParent_bucketScale S hrho P k r hr label W
  have htPow : ((1 / 3456 : NNReal) : ENNReal) ^ 3 <=
      ((t : NNReal) : ENNReal) ^ 3 := by
    exact pow_le_pow_left' (by exact_mod_cast ht) 3
  have hcontainer :=
    selectedParentBucketNormalizedJohnContainer_volume_le_jacobian_fixed
      hfineContained S hrho hrhoOne P k r hr label
  have hvolume : ((t : NNReal) : ENNReal) ^ 3 <=
      JB * (2304 : ENNReal) ^ 3 := by
    rw [volume_selectedParentBucketNormalizedJohnContainer] at hcontainer
    simpa only [t, JB, e] using hcontainer
  have hbase : (1 : ENNReal) <=
      (3456 : ENNReal) ^ 3 * (JB * (2304 : ENNReal) ^ 3) := by
    calc
      (1 : ENNReal) = (3456 : ENNReal) ^ 3 *
          ((1 / 3456 : NNReal) : ENNReal) ^ 3 :=
        one_eq_3456_cube_mul_coe_inverse_cube
      _ <= (3456 : ENNReal) ^ 3 * ((t : NNReal) : ENNReal) ^ 3 := by
        gcongr
      _ <= (3456 : ENNReal) ^ 3 *
          (JB * (2304 : ENNReal) ^ 3) := by gcongr
  have hcenter : JC = (1 / 8 : ENNReal) * JB := by
    dsimp only [JC]
    rw [affineJacobian_centeredHalfPostBucketAffineEquiv,
      halfPostBucketAffineJacobian]
  have hcancel : (8 : ENNReal) * (1 / 8 : ENNReal) = 1 := by
    simp only [div_eq_mul_inv, one_mul]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  calc
    (1 : ENNReal) <=
        (3456 : ENNReal) ^ 3 * (JB * (2304 : ENNReal) ^ 3) := hbase
    _ = centeredAdaptiveJacobianInverseConstant * JC := by
      rw [hcenter]
      unfold centeredAdaptiveJacobianInverseConstant
      calc
        (3456 : ENNReal) ^ 3 * (JB * (2304 : ENNReal) ^ 3) =
            ((8 : ENNReal) * (1 / 8 : ENNReal)) *
              ((3456 : ENNReal) ^ 3 * (JB * (2304 : ENNReal) ^ 3)) := by
          rw [hcancel, one_mul]
        _ = (8 * (3456 : ENNReal) ^ 3 * (2304 : ENNReal) ^ 3) *
              ((1 / 8 : ENNReal) * JB) := by ring

#print axioms one_div_3456_le_selectedParent_bucketScale
#print axioms
  one_le_centeredAdaptiveJacobianInverseConstant_mul_affineJacobian

end
end Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV8
