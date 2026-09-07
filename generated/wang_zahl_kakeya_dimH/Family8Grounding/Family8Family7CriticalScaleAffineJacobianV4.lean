import Family8Grounding.Family8Family7NativeHighCriticalScaleAffineMapV1
import FamilyStickyGrounding.Family6AffineConvexVolumeCoreV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped ENNReal NNReal Matrix

namespace Family8Family7CriticalScaleAffineJacobianV4

open LeanEval.Analysis.WangZahlKakeya
open Family6AffineConvexVolumeCoreV1
open Family8Family7NativeHighCriticalScaleAffineMapV1
open FamilyStickyWZ2ProjectionSliceRetentionV1

noncomputable section

/-!
# Exact Jacobian of the critical-scale graph normalization, V4

V1--V3 were failed matrix-rewrite drafts and are intentionally not imported.
-/

theorem criticalScaleLinearEquiv_det
    (t : Real) (ht : 0 < t) (c0 d0 : Real) :
    LinearMap.det
        (criticalScaleLinearEquiv t ht c0 d0 : Space →ₗ[Real] Space) =
      1 / (4096 * t ^ 2) := by
  let L : Space →ₗ[Real] Space :=
    (criticalScaleLinearEquiv t ht c0 d0 : Space →ₗ[Real] Space)
  let b := (EuclideanSpace.basisFun (Fin 3) Real).toBasis
  have hmatrix : LinearMap.toMatrix b b L =
      !![1 / (16 * t), 0, -c0 / (16 * t);
         0, 1 / (16 * t), -d0 / (16 * t);
         0, 0, 1 / 16] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, L, b, criticalScaleLinearEquiv,
        point3]
  calc
    LinearMap.det
        (criticalScaleLinearEquiv t ht c0 d0 : Space →ₗ[Real] Space) =
        Matrix.det (LinearMap.toMatrix b b L) := by
          exact (LinearMap.det_toMatrix b L).symm
    _ = 1 / (4096 * t ^ 2) := by
      rw [hmatrix, Matrix.det_fin_three]
      simp
      field_simp [ht.ne']
      ring

theorem affineJacobian_criticalScaleAffineEquiv
    (t : Real) (ht : 0 < t) (a0 b0 c0 d0 : Real) :
    affineJacobian (criticalScaleAffineEquiv t ht a0 b0 c0 d0) =
      (1 : ENNReal) / (4096 * ENNReal.ofReal t ^ 2) := by
  unfold affineJacobian
  rw [criticalScaleAffineEquiv_linear,
    criticalScaleLinearEquiv_det]
  have ht0 : 0 ≤ t := ht.le
  have hdenPos : 0 < 4096 * t ^ 2 := by positivity
  rw [abs_of_pos (div_pos (by norm_num) hdenPos)]
  rw [ENNReal.ofReal_div_of_pos hdenPos]
  norm_num [ENNReal.ofReal_mul ht0, ENNReal.ofReal_pow ht0 2]

#print axioms criticalScaleLinearEquiv_det
#print axioms affineJacobian_criticalScaleAffineEquiv

end
end Family8Family7CriticalScaleAffineJacobianV4
