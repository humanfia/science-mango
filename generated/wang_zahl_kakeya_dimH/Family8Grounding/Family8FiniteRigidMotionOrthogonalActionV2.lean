import Family8Grounding.Family8FiniteRigidMotionOrthogonalHaarV4
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace
open scoped Matrix.Norms.L2Operator

namespace Family8FiniteRigidMotionOrthogonalActionV2

open LeanEval.Analysis.WangZahlKakeya
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRigidMotionOrthogonalHaarV4

noncomputable section

/-!
# The Haar orthogonal matrix as an actual rigid motion

The matrix-to-operator equivalence is a star-algebra equivalence, hence it
sends every member of `O(3)` to a unitary continuous linear endomorphism.
Mathlib's unitary/linear-isometry equivalence then supplies the inverse from
the unitary identities themselves.  Thus no action or surjectivity callback
is stored as data.
-/

def orthogonalThreeCLM (U : OrthogonalThree) : Space →L[Real] Space :=
  (Matrix.toEuclideanCLM :
    Matrix (Fin 3) (Fin 3) Real ≃⋆ₐ[Real]
      (Space →L[Real] Space)).toFun U.1

theorem orthogonalThreeCLM_mem_unitary (U : OrthogonalThree) :
    orthogonalThreeCLM U ∈ unitary (Space →L[Real] Space) := by
  exact Unitary.map_mem
    (Matrix.toEuclideanCLM :
      Matrix (Fin 3) (Fin 3) Real ≃⋆ₐ[Real]
        (Space →L[Real] Space)) U.2

def orthogonalThreeUnitary (U : OrthogonalThree) :
    unitary (Space →L[Real] Space) :=
  ⟨orthogonalThreeCLM U, orthogonalThreeCLM_mem_unitary U⟩

def orthogonalThreeLinearIsometryEquiv (U : OrthogonalThree) :
    Space ≃ₗᵢ[Real] Space :=
  Unitary.linearIsometryEquiv (orthogonalThreeUnitary U)

@[simp] theorem orthogonalThreeLinearIsometryEquiv_apply
    (U : OrthogonalThree) (x : Space) :
    orthogonalThreeLinearIsometryEquiv U x = orthogonalThreeCLM U x :=
  rfl

@[simp] theorem orthogonalThreeLinearIsometryEquiv_norm
    (U : OrthogonalThree) (x : Space) :
    ‖orthogonalThreeLinearIsometryEquiv U x‖ = ‖x‖ := by
  exact (orthogonalThreeLinearIsometryEquiv U).norm_map x

/-- The actual rotation in the repository's rigid-motion type. -/
def orthogonalThreeRigidMotion (U : OrthogonalThree) : RigidMotion :=
  (orthogonalThreeLinearIsometryEquiv U).toAffineIsometryEquiv

@[simp] theorem orthogonalThreeRigidMotion_apply
    (U : OrthogonalThree) (x : Space) :
    orthogonalThreeRigidMotion U x = orthogonalThreeCLM U x := by
  rfl

@[simp] theorem orthogonalThreeRigidMotion_zero (U : OrthogonalThree) :
    orthogonalThreeRigidMotion U 0 = 0 := by
  simp

theorem orthogonalThreeRigidMotion_norm
    (U : OrthogonalThree) (x : Space) :
    ‖orthogonalThreeRigidMotion U x‖ = ‖x‖ := by
  simp only [orthogonalThreeRigidMotion_apply]
  exact (orthogonalThreeLinearIsometryEquiv_norm U x)

#print axioms orthogonalThreeCLM_mem_unitary
#print axioms orthogonalThreeLinearIsometryEquiv_apply
#print axioms orthogonalThreeLinearIsometryEquiv_norm
#print axioms orthogonalThreeRigidMotion_apply
#print axioms orthogonalThreeRigidMotion_norm

end
end Family8FiniteRigidMotionOrthogonalActionV2
