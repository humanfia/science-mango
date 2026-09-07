import Family8Grounding.Family8SelectedParentPlankHalfPostKatzTaoV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open scoped ENNReal NNReal

namespace Family8SelectedParentPlankHalfPostKatzTaoV3

open LeanEval.Analysis.WangZahlKakeya
open Family6AffineConvexVolumeCoreV1
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankHalfPostMapCarrierV2

noncomputable section

/-!
# Exact constant costs of the selected-bucket half post-map

In dimension three the post-dilation has Jacobian `1/8`.  Its linear
operator norm is exactly one half of the original common bucket map's norm.
-/

theorem affineJacobian_trans
    (e f : Space ≃ᵃ[Real] Space) :
    affineJacobian (e.trans f) = affineJacobian f * affineJacobian e := by
  unfold affineJacobian
  change ENNReal.ofReal
      |LinearMap.det
        ((f.linear : Space →ₗ[Real] Space).comp
          (e.linear : Space →ₗ[Real] Space))| =
    ENNReal.ofReal |LinearMap.det (f.linear : Space →ₗ[Real] Space)| *
      ENNReal.ofReal |LinearMap.det (e.linear : Space →ₗ[Real] Space)|
  rw [LinearMap.det_comp, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]

theorem halfScalarDilationLinearEquiv_det :
    LinearMap.det
      (scalarDilationLinearEquiv (2 : NNReal)⁻¹ (by norm_num) :
        Space →ₗ[Real] Space) = (1 / 8 : Real) := by
  have hmap :
      (scalarDilationLinearEquiv (2 : NNReal)⁻¹ (by norm_num) :
        Space →ₗ[Real] Space) =
        (1 / 2 : Real) • LinearMap.id := by
    ext x
    simp [scalarDilationLinearEquiv]
  rw [hmap, LinearMap.det_smul, LinearMap.det_id]
  norm_num

theorem halfScalarDilationAffineJacobian :
    affineJacobian
      (scalarDilationAffineEquiv (2 : NNReal)⁻¹ (by norm_num)) =
        (1 / 8 : ENNReal) := by
  unfold affineJacobian scalarDilationAffineEquiv
  have hlinear :
      ((scalarDilationLinearEquiv (2 : NNReal)⁻¹
        (by norm_num)).toAffineEquiv).linear =
          (scalarDilationLinearEquiv (2 : NNReal)⁻¹
            (by norm_num)) := rfl
  rw [hlinear, halfScalarDilationLinearEquiv_det]
  rw [abs_of_nonneg (by norm_num : (0 : Real) ≤ 1 / 8)]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : Real) < 8)]
  norm_num

theorem halfPostBucketAffineJacobian
    (e : Space ≃ᵃ[Real] Space) (label : Fin 3 → Int) :
    affineJacobian (halfPostBucketAffineEquiv e label) =
      (1 / 8 : ENNReal) *
        affineJacobian (bucketNormalizedAffineEquiv e label) := by
  rw [halfPostBucketAffineEquiv, affineJacobian_trans,
    halfScalarDilationAffineJacobian]

theorem affineLinearOperatorNorm_halfPostBucketAffineEquiv
    (e : Space ≃ᵃ[Real] Space) (label : Fin 3 → Int) :
    affineLinearOperatorNorm (halfPostBucketAffineEquiv e label) =
      (1 / 2 : Real) *
        affineLinearOperatorNorm (bucketNormalizedAffineEquiv e label) := by
  unfold affineLinearOperatorNorm
  have hmap :
      LinearMap.toContinuousLinearMap
          (halfPostBucketAffineEquiv e label).linear.toLinearMap =
        (1 / 2 : Real) •
          LinearMap.toContinuousLinearMap
            (bucketNormalizedAffineEquiv e label).linear.toLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    change (halfPostBucketAffineEquiv e label).linear x =
      (1 / 2 : Real) • (bucketNormalizedAffineEquiv e label).linear x
    rw [halfPostBucketAffineEquiv]
    change scalarDilationLinearEquiv (2 : NNReal)⁻¹ (by norm_num)
      ((bucketNormalizedAffineEquiv e label).linear x) =
        (1 / 2 : Real) • (bucketNormalizedAffineEquiv e label).linear x
    simp [scalarDilationLinearEquiv]
  rw [hmap, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]

#print axioms affineJacobian_trans
#print axioms halfScalarDilationLinearEquiv_det
#print axioms halfScalarDilationAffineJacobian
#print axioms halfPostBucketAffineJacobian
#print axioms affineLinearOperatorNorm_halfPostBucketAffineEquiv

end
end Family8SelectedParentPlankHalfPostKatzTaoV3
