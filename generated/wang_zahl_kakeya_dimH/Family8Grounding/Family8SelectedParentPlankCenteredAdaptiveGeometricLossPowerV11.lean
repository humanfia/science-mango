import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV8

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV11

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV2
open Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV8
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8SelectedParentPlankCenteredHalfPostCarrierV1
open Family8SelectedParentPlankCenteredSourcePowerEnvelopesV4
open Family8SelectedParentPlankFineProxyKatzTaoV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

theorem affineAxisProxyVolumeRatio_eq_sixteen_mul_scaleRatio_sq
    {delta s : NNReal} (hdelta : 0 < delta) :
    affineAxisProxyVolumeRatio delta s =
      16 * (((s : ENNReal) / (delta : ENNReal)) ^ 2) := by
  have hleftTop : affineAxisProxyVolumeRatio delta s ≠ ∞ := by
    unfold affineAxisProxyVolumeRatio
    apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top (by norm_num)
        (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    · exact ENNReal.div_ne_zero.mpr
        ⟨pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hdelta.ne'), by norm_num⟩
  have hrightTop :
      16 * (((s : ENNReal) / (delta : ENNReal)) ^ 2) ≠ ∞ := by
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.pow_ne_top
        (ENNReal.div_ne_top ENNReal.coe_ne_top
          (ENNReal.coe_ne_zero.mpr hdelta.ne')))
  apply (ENNReal.toReal_eq_toReal_iff' hleftTop hrightTop).mp
  have hdeltaReal : (0 : Real) < (delta : Real) := by exact_mod_cast hdelta
  norm_num [affineAxisProxyVolumeRatio, ENNReal.toReal_div,
    ENNReal.toReal_mul, ENNReal.toReal_pow]
  field_simp [hdeltaReal.ne']
  ring

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The honest volume/Jacobian loss is at most a fixed constant times the
square of the literal proxy/source scale ratio. -/
theorem selectedParent_centered_geometricLoss_le_fixed_mul_scaleRatio_sq
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
      S (blockAt S.activeCoarseFamily P k).fiber hrho label})
    (s : NNReal) (hdelta : 0 < delta) :
    centeredHalfPostSelectedPlankFineProxyGeometricLoss
        s
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho label hplank W <=
      centeredAdaptiveGeometricLossFixedConstant *
        (((s : ENNReal) / (delta : ENNReal)) ^ 2) := by
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let J : ENNReal := affineJacobian
    (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W)
  let ratio : ENNReal := affineAxisProxyVolumeRatio delta s
  have hJ0 : J ≠ 0 :=
    (affineJacobian_pos
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W)).ne'
  have hJTop : J ≠ ∞ := affineJacobian_ne_top _
  have hJbound : 1 <= centeredAdaptiveJacobianInverseConstant * J := by
    simpa only [J, e, B] using
      one_le_centeredAdaptiveJacobianInverseConstant_mul_affineJacobian
        hfineContained S hrho hrhoOne P k r hr label hplank W
  unfold centeredHalfPostSelectedPlankFineProxyGeometricLoss
  change ratio / J <= _
  apply (ENNReal.div_le_iff hJ0 hJTop).2
  calc
    ratio <= ratio *
        (centeredAdaptiveJacobianInverseConstant * J) := by
      calc
        ratio = ratio * 1 := by rw [mul_one]
        _ <= ratio *
            (centeredAdaptiveJacobianInverseConstant * J) := by gcongr
    _ = (centeredAdaptiveJacobianInverseConstant * ratio) * J := by ring
    _ = (centeredAdaptiveGeometricLossFixedConstant *
          (((s : ENNReal) / (delta : ENNReal)) ^ 2)) * J := by
      rw [show ratio = 16 *
          (((s : ENNReal) / (delta : ENNReal)) ^ 2) by
        simpa only [ratio] using
          affineAxisProxyVolumeRatio_eq_sixteen_mul_scaleRatio_sq hdelta]
      unfold centeredAdaptiveGeometricLossFixedConstant
      ring

/-- Specialization of the preceding estimate to the radius-adaptive scale
used by the packing endpoint. -/
theorem selectedParent_centered_adaptive_geometricLoss_le_fixed_mul_scaleRatio_sq
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
      S (blockAt S.activeCoarseFamily P k).fiber hrho label})
    (hdelta : 0 < delta) :
    centeredHalfPostSelectedPlankFineProxyGeometricLoss
        (selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r label)
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho label hplank W <=
      centeredAdaptiveGeometricLossFixedConstant *
        ((((selectedParentCenteredHalfPostAdaptiveProxyScale
          delta rho r label : NNReal) : ENNReal) /
            (delta : ENNReal)) ^ 2) := by
  exact selectedParent_centered_geometricLoss_le_fixed_mul_scaleRatio_sq
    hfineContained S hrho hrhoOne P k r hr label hplank W _ hdelta

#print axioms affineAxisProxyVolumeRatio_eq_sixteen_mul_scaleRatio_sq
#print axioms
  selectedParent_centered_geometricLoss_le_fixed_mul_scaleRatio_sq
#print axioms
  selectedParent_centered_adaptive_geometricLoss_le_fixed_mul_scaleRatio_sq

end
end Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV11
