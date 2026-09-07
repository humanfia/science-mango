import Family8Grounding.Family8FiniteRigidMotionOrthogonalActionV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace
open scoped Matrix.Norms.L2Operator

namespace Family8FiniteRigidMotionOrthogonalOrbitV3

open LeanEval.Analysis.WangZahlKakeya
open Family8FiniteRigidMotionOrthogonalHaarV4
open Family8FiniteRigidMotionOrthogonalActionV2

noncomputable section

/-!
# Continuous measurable O(3) orbit action

The L2 operator norm on matrices is induced by `toEuclideanCLM`.  Bundling
that linear equivalence as a continuous linear map makes evaluation at a
fixed vector manifestly continuous, hence measurable for Haar pushforward.
-/

def matrixToEuclideanCLM :
    Matrix (Fin 3) (Fin 3) Real →L[Real] (Space →L[Real] Space) :=
  LinearMap.mkContinuous
    (Matrix.toEuclideanCLM :
      Matrix (Fin 3) (Fin 3) Real ≃⋆ₐ[Real]
        (Space →L[Real] Space)).toStarAlgHom.toAlgHom.toLinearMap
    1
    (fun A ↦ by
      rw [one_mul]
      exact le_of_eq (Matrix.l2_opNorm_toEuclideanCLM A))

@[simp] theorem matrixToEuclideanCLM_apply
    (A : Matrix (Fin 3) (Fin 3) Real) :
    matrixToEuclideanCLM A =
      (Matrix.toEuclideanCLM :
        Matrix (Fin 3) (Fin 3) Real ≃⋆ₐ[Real]
          (Space →L[Real] Space)).toFun A :=
  rfl

def orthogonalOrbit (u : Space) (U : OrthogonalThree) : Space :=
  orthogonalThreeCLM U u

theorem continuous_orthogonalOrbit (u : Space) :
    Continuous (orthogonalOrbit u) := by
  have hoperator : Continuous
      (fun U : OrthogonalThree ↦ matrixToEuclideanCLM U.1) :=
    matrixToEuclideanCLM.continuous.comp continuous_subtype_val
  have heval : Continuous
      (fun U : OrthogonalThree ↦ matrixToEuclideanCLM U.1 u) :=
    ((ContinuousLinearMap.apply Real Space) u).continuous.comp hoperator
  change Continuous
    (fun U : OrthogonalThree ↦
      (Matrix.toEuclideanCLM :
        Matrix (Fin 3) (Fin 3) Real ≃⋆ₐ[Real]
          (Space →L[Real] Space)).toFun U.1 u)
  simpa only [matrixToEuclideanCLM_apply] using heval

theorem measurable_orthogonalOrbit (u : Space) :
    Measurable (orthogonalOrbit u) :=
  (continuous_orthogonalOrbit u).measurable

@[simp] theorem norm_orthogonalOrbit (u : Space) (U : OrthogonalThree) :
    ‖orthogonalOrbit u U‖ = ‖u‖ := by
  exact orthogonalThreeLinearIsometryEquiv_norm U u

theorem orthogonalThreeCLM_mul
    (U V : OrthogonalThree) (x : Space) :
    orthogonalThreeCLM (U * V) x =
      orthogonalThreeCLM U (orthogonalThreeCLM V x) := by
  let e : Matrix (Fin 3) (Fin 3) Real ≃⋆ₐ[Real]
      (Space →L[Real] Space) := Matrix.toEuclideanCLM
  have hmap : e.toFun (U.1 * V.1) = e.toFun U.1 * e.toFun V.1 :=
    e.map_mul U.1 V.1
  change (e.toFun (U.1 * V.1)) x =
    (e.toFun U.1) ((e.toFun V.1) x)
  rw [hmap]
  rfl

theorem orthogonalOrbit_mul
    (u : Space) (U V : OrthogonalThree) :
    orthogonalOrbit u (U * V) =
      orthogonalThreeCLM U (orthogonalOrbit u V) := by
  exact orthogonalThreeCLM_mul U V u

#print axioms continuous_orthogonalOrbit
#print axioms measurable_orthogonalOrbit
#print axioms norm_orthogonalOrbit
#print axioms orthogonalThreeCLM_mul
#print axioms orthogonalOrbit_mul

end
end Family8FiniteRigidMotionOrthogonalOrbitV3
