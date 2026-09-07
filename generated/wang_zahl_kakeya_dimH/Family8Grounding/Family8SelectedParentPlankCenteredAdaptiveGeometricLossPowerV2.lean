import Family8Grounding.Family8SelectedParentPlankCenteredSourcePowerEnvelopesV4
import Family8Grounding.Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
import Family8Grounding.Family8SelectedParentBucketContainerJacobianEnvelopeV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV2

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
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8SelectedParentPlankCenteredHalfPostCarrierV1
open Family8SelectedParentPlankCenteredSourcePowerEnvelopesV4
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# The actual geometric loss at the adaptive selected-parent scale

The selected bucket is not an arbitrary affine normalization. Its label is
the dyadic label of an actual member of the winning block. Consequently its
long side endpoint is at most `3456 * r`. Combining that fact with the
already proved volume/Jacobian identity for the winning-hull John box gives a
fixed lower bound for the centered bucket Jacobian.

After this cancellation, the exact geometric loss is bounded by one fixed
constant times `(s / delta)^2`. A genuine scale relation `s^k <= delta`
then turns it into an `s`-negative power; no geometric-loss callback is used.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

def centeredAdaptiveJacobianInverseConstant : ENNReal :=
  8 * (3456 : ENNReal) ^ 3 * (2304 : ENNReal) ^ 3

def centeredAdaptiveGeometricLossFixedConstant : ENNReal :=
  16 * centeredAdaptiveJacobianInverseConstant

def centeredAdaptiveGeometricLossThreshold (absorbEta : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    centeredAdaptiveGeometricLossFixedConstant absorbEta

theorem centeredAdaptiveJacobianInverseConstant_ne_top :
    centeredAdaptiveJacobianInverseConstant ≠ ∞ := by
  norm_num [centeredAdaptiveJacobianInverseConstant]

theorem centeredAdaptiveGeometricLossFixedConstant_ne_top :
    centeredAdaptiveGeometricLossFixedConstant ≠ ∞ := by
  norm_num [centeredAdaptiveGeometricLossFixedConstant,
    centeredAdaptiveJacobianInverseConstant]

theorem centeredAdaptiveGeometricLossThreshold_pos (absorbEta : Real) :
    0 < centeredAdaptiveGeometricLossThreshold absorbEta :=
  finiteConstantSmallDeltaThreshold_pos _ _

/-- The selected label's dyadic long-side endpoint is controlled by the
actual contraction scale. -/
theorem selectedParent_sideShapeUpper_two_le_3456_mul_r
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
    sideShapeUpper label 2 <= 3456 * r := by
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let side := selectedParentLongRelabeledSide e S B hrho W.1
  have hsidePos : forall i, 0 < side i := by
    intro i
    exact selectedParentLongRelabeledSide_pos e S B hrho W.1 i
  have hlabel : sideShapeLabel side = label := by
    exact (mem_sideShapeBucket_iff Finset.univ
      (fun p => selectedParentLongRelabeledSide e S B hrho p)
      label W.1).mp W.2 |>.2
  have hband := (sideShapeUpper_half_lt_and_le hsidePos 2).1
  rw [hlabel] at hband
  have hsideUpper : side 2 <= 1728 * r := by
    simpa only [side, e, B] using
      selectedParentContractedLongRelabeledSide_le
        S hrho P k r hr W.1 2
  calc
    sideShapeUpper label 2 <= 2 * side 2 := by
      simpa [mul_comm] using
        le_of_lt ((div_lt_iff₀ (by norm_num : (0 : NNReal) < 2)).mp hband)
    _ <= 2 * (1728 * r) := by gcongr
    _ = 3456 * r := by ring

#print axioms centeredAdaptiveJacobianInverseConstant_ne_top
#print axioms centeredAdaptiveGeometricLossFixedConstant_ne_top
#print axioms centeredAdaptiveGeometricLossThreshold_pos
#print axioms selectedParent_sideShapeUpper_two_le_3456_mul_r

end
end Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV2
