import Family8Grounding.Family8FiniteRigidMotionDirectionReflectionV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionDirectionTranslationSupportV1

open LeanEval.Analysis.WangZahlKakeya
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRigidMotionDirectionReflectionV2

noncomputable section

/-!
# Translation support for the direction-changing rigid motion

The paper samples a rotation together with a translation of size at most
one.  This file forms that literal affine isometry and proves the B2 support
needed before eighth-normalization.
-/

def directionTranslationRigidMotion
    (u v t : Space) : RigidMotion :=
  (directionRigidMotion u v).trans
    (AffineIsometryEquiv.constVAdd Real Space t)

@[simp] theorem directionTranslationRigidMotion_apply
    (u v t x : Space) :
    directionTranslationRigidMotion u v t x =
      t + directionReflection u v x := by
  rfl

theorem directionTranslationRigidMotion_maps_of_norm_eq
    {u v t : Space} (h : ‖u‖ = ‖v‖) :
    directionTranslationRigidMotion u v t u = t + v := by
  rw [directionTranslationRigidMotion_apply,
    directionReflection_apply_of_norm_eq h]

theorem directionTranslationRigidMotion_mem_closedBall_two
    {u v t x : Space}
    (ht : ‖t‖ ≤ 1)
    (hx : x ∈ Metric.closedBall (0 : Space) 1) :
    directionTranslationRigidMotion u v t x ∈
      Metric.closedBall (0 : Space) 2 := by
  rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  rw [directionTranslationRigidMotion_apply]
  calc
    ‖t + directionReflection u v x‖ ≤
        ‖t‖ + ‖directionReflection u v x‖ := norm_add_le _ _
    _ = ‖t‖ + ‖x‖ := by
      rw [(directionReflection u v).norm_map]
    _ ≤ 2 := by linarith

theorem directionTranslationRigidMotion_image_unitBall_subset_two
    {u v t : Space} (ht : ‖t‖ ≤ 1) :
    directionTranslationRigidMotion u v t ''
        Metric.closedBall (0 : Space) 1 ⊆
      Metric.closedBall (0 : Space) 2 := by
  rintro _ ⟨x, hx, rfl⟩
  exact directionTranslationRigidMotion_mem_closedBall_two ht hx

#print axioms directionTranslationRigidMotion_maps_of_norm_eq
#print axioms directionTranslationRigidMotion_mem_closedBall_two
#print axioms directionTranslationRigidMotion_image_unitBall_subset_two

end
end Family8FiniteRigidMotionDirectionTranslationSupportV1
