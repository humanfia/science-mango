import Family8Grounding.Family8FiniteRandomRigidMotionB2NormalizationCoreV1
import FamilyStickyGrounding.Family6AffineConvexVolumeCoreV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionB2DilationVolumeV1

open LeanEval.Analysis.WangZahlKakeya
open Family6AffineConvexVolumeCoreV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1

noncomputable section

/-!
# Exact volume scaling for the eighth-dilation
-/

/-- Scalar multiplication by `1/8` as a genuine linear equivalence. -/
def eighthDilationLinearEquiv : Space ≃ₗ[Real] Space where
  toFun x := (1 / 8 : Real) • x
  invFun x := (8 : Real) • x
  left_inv x := by module
  right_inv x := by module
  map_add' x y := by module
  map_smul' c x := by
    simp only [smul_smul, RingHom.id_apply]
    rw [mul_comm]

@[simp] theorem eighthDilationLinearEquiv_apply (x : Space) :
    eighthDilationLinearEquiv x = eighthDilationPoint x := rfl

/-- The corresponding origin-fixing affine equivalence. -/
def eighthDilationAffineEquiv : Space ≃ᵃ[Real] Space :=
  eighthDilationLinearEquiv.toAffineEquiv

@[simp] theorem eighthDilationAffineEquiv_apply (x : Space) :
    eighthDilationAffineEquiv x = eighthDilationPoint x := rfl

theorem eighthDilationLinearEquiv_det :
    LinearMap.det (eighthDilationLinearEquiv : Space →ₗ[Real] Space) =
      (1 / 512 : Real) := by
  have hlinear :
      (eighthDilationLinearEquiv : Space →ₗ[Real] Space) =
        (1 / 8 : Real) • LinearMap.id := by
    ext x
    simp [eighthDilationLinearEquiv]
  rw [hlinear, LinearMap.det_smul, LinearMap.det_id]
  norm_num

/-- The absolute affine Jacobian is the three-dimensional factor `8^-3`. -/
theorem eighthDilationAffineJacobian :
    affineJacobian eighthDilationAffineEquiv = (1 / 512 : ENNReal) := by
  unfold affineJacobian
  have hlinear :
      eighthDilationAffineEquiv.linear =
        (eighthDilationLinearEquiv : Space →ₗ[Real] Space) := rfl
  rw [hlinear, eighthDilationLinearEquiv_det]
  rw [abs_of_nonneg (by norm_num : (0 : Real) ≤ 1 / 512)]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : Real) < 512)]
  norm_num

/-- Every measurable or nonmeasurable set has the same exact outer-volume
scaling under the affine eighth-dilation. -/
theorem volume_image_eighthDilationPoint (s : Set Space) :
    volume (eighthDilationPoint '' s) =
      (1 / 512 : ENNReal) * volume s := by
  have h := volume_image_affineEquiv eighthDilationAffineEquiv s
  change volume (eighthDilationPoint '' s) =
    affineJacobian eighthDilationAffineEquiv * volume s at h
  simpa only [eighthDilationAffineJacobian] using h

#print axioms eighthDilationLinearEquiv_det
#print axioms eighthDilationAffineJacobian
#print axioms volume_image_eighthDilationPoint

end
end Family8FiniteRandomRigidMotionB2DilationVolumeV1
