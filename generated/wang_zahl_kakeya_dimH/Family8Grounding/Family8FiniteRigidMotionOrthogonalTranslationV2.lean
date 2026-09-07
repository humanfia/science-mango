import Family8Grounding.Family8FiniteRigidMotionOrthogonalOrbitV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalTranslationV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRigidMotionOrthogonalHaarV4
open Family8FiniteRigidMotionOrthogonalActionV2
open Family8FiniteRigidMotionOrthogonalOrbitV3

noncomputable section

/-!
# The genuine rotation-plus-translation rigid motion

The orthogonal Haar outcome supplies the linear part and an arbitrary vector
supplies the translation.  Translation does not alter the moved tube's axis
direction, so direction incidences can be estimated uniformly in that vector.
-/

def orthogonalTranslationRigidMotion
    (U : OrthogonalThree) (t : Space) : RigidMotion :=
  (orthogonalThreeRigidMotion U).trans
    (AffineIsometryEquiv.constVAdd Real Space t)

@[simp] theorem orthogonalTranslationRigidMotion_apply
    (U : OrthogonalThree) (t x : Space) :
    orthogonalTranslationRigidMotion U t x =
      t + orthogonalThreeCLM U x := by
  rfl

@[simp] theorem orthogonalTranslationRigidMotion_linear
    (U : OrthogonalThree) (t : Space) :
    (orthogonalTranslationRigidMotion U t).linearIsometryEquiv =
      orthogonalThreeLinearIsometryEquiv U := by
  ext x
  rfl

@[simp] theorem rigidTube_orthogonalTranslation_direction
    {delta : NNReal} (T : Tube delta)
    (U : OrthogonalThree) (t : Space) :
    (rigidTube (orthogonalTranslationRigidMotion U t) T).axis.direction =
      orthogonalOrbit T.axis.direction U := by
  rw [rigidTube_axis, rigidUnitSegment_direction,
    orthogonalTranslationRigidMotion_linear]
  rfl

theorem orthogonalTranslationRigidMotion_mem_closedBall_two
    {U : OrthogonalThree} {t x : Space}
    (ht : ‖t‖ ≤ 1)
    (hx : x ∈ Metric.closedBall (0 : Space) 1) :
    orthogonalTranslationRigidMotion U t x ∈
      Metric.closedBall (0 : Space) 2 := by
  rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  rw [orthogonalTranslationRigidMotion_apply]
  calc
    ‖t + orthogonalThreeCLM U x‖ ≤
        ‖t‖ + ‖orthogonalThreeCLM U x‖ := norm_add_le _ _
    _ = ‖t‖ + ‖x‖ := by
      rw [← orthogonalThreeLinearIsometryEquiv_apply,
        orthogonalThreeLinearIsometryEquiv_norm]
    _ ≤ 2 := by linarith

theorem orthogonalTranslationRigidMotion_image_unitBall_subset_two
    {U : OrthogonalThree} {t : Space} (ht : ‖t‖ ≤ 1) :
    orthogonalTranslationRigidMotion U t ''
        Metric.closedBall (0 : Space) 1 ⊆
      Metric.closedBall (0 : Space) 2 := by
  rintro _ ⟨x, hx, rfl⟩
  exact orthogonalTranslationRigidMotion_mem_closedBall_two ht hx

#print axioms orthogonalTranslationRigidMotion_apply
#print axioms orthogonalTranslationRigidMotion_linear
#print axioms rigidTube_orthogonalTranslation_direction
#print axioms orthogonalTranslationRigidMotion_mem_closedBall_two
#print axioms orthogonalTranslationRigidMotion_image_unitBall_subset_two

end
end Family8FiniteRigidMotionOrthogonalTranslationV2
