import Family8Grounding.Family8FiniteRigidMotionOrthogonalOrbitV3
import Family8Grounding.Family8FiniteRigidMotionDirectionReflectionV2
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace
open scoped Matrix.Norms.L2Operator

namespace Family8FiniteRigidMotionOrthogonalTransitiveV2

open LeanEval.Analysis.WangZahlKakeya
open Family8FiniteRigidMotionOrthogonalHaarV4
open Family8FiniteRigidMotionOrthogonalActionV2
open Family8FiniteRigidMotionOrthogonalOrbitV3
open Family8FiniteRigidMotionDirectionReflectionV2

noncomputable section

/-!
# Transitivity of the actual O(3) orbit

The already grounded hyperplane reflection is converted back to its matrix in
the standard orthonormal basis.  The matrix is proved orthogonal by the
general Mathlib theorem for linear isometries, and `toLin_toMatrix` proves
that the resulting Haar action is exactly the original reflection.
-/

def orthogonalThreeOfLinearIsometry
    (f : Space ≃ₗᵢ[Real] Space) : OrthogonalThree :=
  ⟨f.toMatrix
      (EuclideanSpace.basisFun (Fin 3) Real).toBasis
      (EuclideanSpace.basisFun (Fin 3) Real).toBasis,
    LinearIsometryEquiv.toMatrix_mem_unitaryGroup f
      (EuclideanSpace.basisFun (Fin 3) Real)
      (EuclideanSpace.basisFun (Fin 3) Real)⟩

theorem orthogonalThreeCLM_ofLinearIsometry_apply
    (f : Space ≃ₗᵢ[Real] Space) (x : Space) :
    orthogonalThreeCLM (orthogonalThreeOfLinearIsometry f) x = f x := by
  change
    Matrix.toEuclideanLin
      (f.toMatrix
        (EuclideanSpace.basisFun (Fin 3) Real).toBasis
        (EuclideanSpace.basisFun (Fin 3) Real).toBasis) x = f x
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  simp

def directionOrthogonal (u v : Space) : OrthogonalThree :=
  orthogonalThreeOfLinearIsometry (directionReflection u v)

theorem directionOrthogonal_apply_of_norm_eq
    {u v : Space} (h : ‖u‖ = ‖v‖) :
    orthogonalThreeCLM (directionOrthogonal u v) u = v := by
  rw [directionOrthogonal, orthogonalThreeCLM_ofLinearIsometry_apply]
  exact directionReflection_apply_of_norm_eq h

theorem exists_orthogonalThree_maps_of_norm_eq
    {u v : Space} (h : ‖u‖ = ‖v‖) :
    ∃ U : OrthogonalThree, orthogonalOrbit u U = v := by
  exact ⟨directionOrthogonal u v, directionOrthogonal_apply_of_norm_eq h⟩

#print axioms orthogonalThreeCLM_ofLinearIsometry_apply
#print axioms directionOrthogonal_apply_of_norm_eq
#print axioms exists_orthogonalThree_maps_of_norm_eq

end
end Family8FiniteRigidMotionOrthogonalTransitiveV2
