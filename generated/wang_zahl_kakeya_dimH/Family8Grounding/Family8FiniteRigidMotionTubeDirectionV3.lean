import Family8Grounding.Family8FiniteRigidMotionLinearDirectionV2

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped NNReal InnerProductSpace

namespace Family8FiniteRigidMotionTubeDirectionV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRigidMotionDirectionReflectionV2
open Family8FiniteRigidMotionDirectionTranslationSupportV1
open Family8FiniteRigidMotionLinearDirectionV2

noncomputable section

/-! The genuine affine direction motion sends the literal axis direction of
an actual project tube to any prescribed unit vector. -/

theorem rigidTube_directionTranslationRigidMotion_direction
    {delta : NNReal} (T : Tube delta) (v t : Space)
    (hv : ‖v‖ = 1) :
    (rigidTube
      (directionTranslationRigidMotion T.axis.direction v t) T).axis.direction =
      v := by
  change
    (directionTranslationRigidMotion
      T.axis.direction v t).linearIsometryEquiv T.axis.direction = v
  rw [directionTranslationRigidMotion_linear_apply]
  exact directionReflection_apply_of_norm_eq
    (T.axis.norm_direction.trans hv.symm)

#print axioms rigidTube_directionTranslationRigidMotion_direction

end
end Family8FiniteRigidMotionTubeDirectionV3
