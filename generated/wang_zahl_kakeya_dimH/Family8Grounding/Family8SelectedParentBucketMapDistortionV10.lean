import Family8Grounding.Family8SelectedParentBucketMapDistortionV8
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped NNReal InnerProductSpace BigOperators

namespace Family8SelectedParentBucketMapDistortionV10

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8SelectedParentBucketMapDistortionV1
open Family8SelectedParentBucketMapDistortionV8
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankStickyDirectionTransportV4
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Automatic operator-norm bound for the actual winning-block bucket map.
The side floor `2ρ` is supplied by its genuine coarse tube. -/
theorem selectedParentBucket_affineLinearOpNorm_le
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int) :
    affineLinearOpNorm
        (bucketNormalizedAffineEquiv
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          label) ≤
      3 * (r : Real) /
        ((2 * (rho : Real)) * (sideShapeUpper label 2 : Real)) := by
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  let d := bucketNormalizedAffineEquiv (contractedJohnAffineEquiv J r hr) label
  have hm : 0 < 2 * rho := mul_pos (by norm_num) hrho
  have hside : ∀ j, 2 * rho ≤ J.side j := by
    intro j
    exact selectedParentGreedyBlockJohnSide_two_mul_rho_le S hrho P k j
  unfold affineLinearOpNorm
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖d.linear v‖ ≤ _
  simpa only [d, J, NNReal.coe_mul, NNReal.coe_ofNat] using
    bucketNormalized_contractedJohn_linear_norm_le
      J (2 * rho) r hm hside hr label v

/-- Canonical transformed-axis lower scale `q = r/(6912 u₂)`. -/
def selectedParentStickyAxisLengthFloor
    (r : NNReal) (label : Fin 3 → Int) : NNReal :=
  r / (6912 * sideShapeUpper label 2)

theorem selectedParentStickyAxisLengthFloor_pos
    {r : NNReal} (hr : 0 < r) (label : Fin 3 → Int) :
    0 < selectedParentStickyAxisLengthFloor r label := by
  exact div_pos hr (mul_pos (by norm_num) (sideShapeUpper_pos label 2))

/-- The transported `14ρ` Sticky direction error is at most `145152q`.
This is the fully structured replacement for the arbitrary operator-norm
callback; the cancellation of `ρ` is explicit. -/
theorem selectedParentBucket_affineError_le_145152_mul_axisLengthFloor
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int) :
    affineLinearOpNorm
        (bucketNormalizedAffineEquiv
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          label) * (14 * (rho : Real)) ≤
      145152 * (selectedParentStickyAxisLengthFloor r label : Real) := by
  have hop := selectedParentBucket_affineLinearOpNorm_le
    S hrho P k r hr label
  have hmul := mul_le_mul_of_nonneg_right hop
    (show (0 : Real) ≤ 14 * (rho : Real) by positivity)
  calc
    affineLinearOpNorm
        (bucketNormalizedAffineEquiv
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          label) * (14 * (rho : Real)) ≤
      (3 * (r : Real) /
        ((2 * (rho : Real)) * (sideShapeUpper label 2 : Real))) *
          (14 * (rho : Real)) := hmul
    _ = 145152 * (selectedParentStickyAxisLengthFloor r label : Real) := by
      have hrhoReal : (0 : Real) < (rho : Real) := by exact_mod_cast hrho
      have huReal : (0 : Real) < (sideShapeUpper label 2 : Real) := by
        exact_mod_cast sideShapeUpper_pos label 2
      simp only [selectedParentStickyAxisLengthFloor, NNReal.coe_div,
        NNReal.coe_mul, NNReal.coe_ofNat]
      field_simp [hrhoReal.ne', huReal.ne']
      norm_num

#print axioms selectedParentBucket_affineLinearOpNorm_le
#print axioms selectedParentStickyAxisLengthFloor_pos
#print axioms selectedParentBucket_affineError_le_145152_mul_axisLengthFloor

end
end Family8SelectedParentBucketMapDistortionV10
