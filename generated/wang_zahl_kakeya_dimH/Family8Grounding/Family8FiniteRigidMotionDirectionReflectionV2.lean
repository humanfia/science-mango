import Family8Grounding.Family8FiniteRandomRigidMotionIncidenceV1
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionDirectionReflectionV2

open LeanEval.Analysis.WangZahlKakeya
open Family8GeneralizedFrostmanMultiplicityV1

noncomputable section

/-!
# A genuine direction-changing rigid motion

Translations alone do not randomize a parallel tube family.  Reflection in
the hyperplane perpendicular to `u - v` is an actual linear isometry which
sends `u` to `v` whenever their norms agree.  This module promotes that
reflection to the repository's `RigidMotion`; it is the concrete rotation
outcome on which the finite fixed-John rotation law can be built.
-/

def directionReflection (u v : Space) : Space ≃ₗᵢ[Real] Space :=
  ((Real ∙ (u - v))ᗮ).reflection

theorem directionReflection_apply_of_norm_eq
    {u v : Space} (h : ‖u‖ = ‖v‖) :
    directionReflection u v u = v := by
  exact Submodule.reflection_sub h

def directionRigidMotion (u v : Space) : RigidMotion :=
  (directionReflection u v).toAffineIsometryEquiv

@[simp] theorem directionRigidMotion_apply (u v x : Space) :
    directionRigidMotion u v x = directionReflection u v x :=
  rfl

@[simp] theorem directionRigidMotion_zero (u v : Space) :
    directionRigidMotion u v 0 = 0 := by
  exact (directionReflection u v).map_zero

theorem directionRigidMotion_maps_of_norm_eq
    {u v : Space} (h : ‖u‖ = ‖v‖) :
    directionRigidMotion u v u = v := by
  exact directionReflection_apply_of_norm_eq h

#print axioms directionReflection_apply_of_norm_eq
#print axioms directionRigidMotion_maps_of_norm_eq

end
end Family8FiniteRigidMotionDirectionReflectionV2
