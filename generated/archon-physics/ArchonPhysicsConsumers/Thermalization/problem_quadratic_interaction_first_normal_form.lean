import ArchonPhysics.QuadraticInteractionFirstNormalForm

/-!
# Consumer: first Hamiltonian-to-kinetic normal-form step

This consumer exposes the exact first normal-form identity used in the
equal-mass periodic alpha-FPUT derivation.  It certifies the microscopic
quadratic interaction equation to effective cubic-feedback step; it does not
assume or assert the subsequent wave kinetic limit.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.QuadraticInteractionFirstNormalForm

noncomputable section

variable {Mode : Type*} [Fintype Mode]

theorem problem_quadratic_interaction_first_normal_form
    (vertex : Mode -> Mode -> Mode -> Complex)
    (mismatch : Mode -> Mode -> Mode -> Real)
    (path : Real -> Mode -> Complex)
    (epsilon : Complex) (time : Real) (out : Mode)
    (hpath : ∀ mode, HasDerivAt (fun s => path s mode)
      (epsilon * quadraticOscillatorySource vertex mismatch (path time) time mode)
      time) :
    HasDerivAt
      (fun s => path s out - epsilon *
        quadraticPrimitiveCorrection vertex mismatch (path s) s out)
      (-(epsilon ^ 2) *
        quadraticCubicNormalFormSource vertex mismatch (path time) time out)
      time :=
  hasDerivAt_firstNormalForm vertex mismatch path epsilon time out hpath

theorem problem_quadratic_normal_form_inverse_gap
    (vertex : Mode -> Mode -> Mode -> Complex)
    (mismatch : Mode -> Mode -> Mode -> Real)
    (amplitude : Mode -> Complex) (time : Real) (out : Mode)
    (gap : Real) (hgap : 0 < gap)
    (hmismatch : ∀ left right, gap ≤ |mismatch out left right|) :
    ‖quadraticPrimitiveCorrection vertex mismatch amplitude time out‖ ≤
      (2 / gap) *
        ∑ left, ∑ right,
          ‖vertex out left right‖ * ‖amplitude left‖ * ‖amplitude right‖ :=
  norm_quadraticPrimitiveCorrection_le vertex mismatch amplitude time out
    gap hgap hmismatch

#print axioms problem_quadratic_interaction_first_normal_form
#print axioms problem_quadratic_normal_form_inverse_gap

end

end ArchonPhysicsConsumers.Thermalization
