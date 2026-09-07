import Family8Grounding.Family8FiniteRigidMotionDirectionTranslationSupportV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped InnerProductSpace

namespace Family8FiniteRigidMotionLinearDirectionV2

open LeanEval.Analysis.WangZahlKakeya
open Family8FiniteRigidMotionDirectionReflectionV2
open Family8FiniteRigidMotionDirectionTranslationSupportV1

noncomputable section

theorem directionTranslationRigidMotion_linear_apply
    (u v t x : Space) :
    (directionTranslationRigidMotion u v t).linearIsometryEquiv x =
      directionReflection u v x := by
  rfl

#print axioms directionTranslationRigidMotion_linear_apply

end
end Family8FiniteRigidMotionLinearDirectionV2
