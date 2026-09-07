import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV12

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV14

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV2
open Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV11
open Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV12
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8SelectedParentPlankCenteredHalfPostCarrierV1
open Family8SelectedParentPlankCenteredSourcePowerEnvelopesV4
open Family8SelectedParentPlankFineProxyKatzTaoV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The actual selected-parent centered geometric loss obeys a negative-power
envelope once the literal adaptive scale satisfies the displayed scale
hierarchy.  The loss is computed from the real affine map; it is not supplied
as a callback or structure field. -/
theorem selectedParent_centered_adaptive_geometricLoss_le_power
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
    (hdelta : 0 < delta)
    {scaleExponent absorbEta : Real}
    (hscale :
      (((selectedParentCenteredHalfPostAdaptiveProxyScale
          delta rho r label : NNReal) : ENNReal) ^ scaleExponent) <=
        (delta : ENNReal))
    (habsorbEta : 0 < absorbEta)
    (hsmall : selectedParentCenteredHalfPostAdaptiveProxyScale
      delta rho r label <=
        centeredAdaptiveGeometricLossThreshold absorbEta) :
    centeredHalfPostSelectedPlankFineProxyGeometricLoss
        (selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r label)
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho label hplank W <=
      (((selectedParentCenteredHalfPostAdaptiveProxyScale
          delta rho r label : NNReal) : ENNReal) ^
        (-(2 * scaleExponent - 2 + absorbEta))) := by
  calc
    centeredHalfPostSelectedPlankFineProxyGeometricLoss
        (selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r label)
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho label hplank W <=
      centeredAdaptiveGeometricLossFixedConstant *
        ((((selectedParentCenteredHalfPostAdaptiveProxyScale
          delta rho r label : NNReal) : ENNReal) /
            (delta : ENNReal)) ^ 2) :=
      selectedParent_centered_adaptive_geometricLoss_le_fixed_mul_scaleRatio_sq
        hfineContained S hrho hrhoOne P k r hr label hplank W hdelta
    _ <= (((selectedParentCenteredHalfPostAdaptiveProxyScale
          delta rho r label : NNReal) : ENNReal) ^
        (-(2 * scaleExponent - 2 + absorbEta))) :=
      centeredAdaptive_fixed_mul_scaleRatio_sq_le_power
        (adaptiveProxyScale_pos r delta rho hr label) hscale habsorbEta hsmall

#print axioms selectedParent_centered_adaptive_geometricLoss_le_power

end
end Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV14
