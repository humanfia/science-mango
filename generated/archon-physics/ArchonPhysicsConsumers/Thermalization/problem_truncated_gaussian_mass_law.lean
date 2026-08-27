import ArchonPhysics.TruncatedGaussianMassLaw

/-!
# Acceptance target: positive truncated-Gaussian masses

This consumer fixes mean one and variance `1 / 100`, checks normalization,
mutual absolute continuity on `[4/5,6/5]`, positive probability of a concrete
interior patch, and positivity of a three-coordinate interior open patch.
-/

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open ArchonPhysics RandomEnsemble

noncomputable section

namespace GaussianMass

open TruncatedGaussianMassLaw

/-- Concrete small-variance Gaussian centered at unit mass. -/
def parameters : Parameters where
  mean := 1
  variance := 1 / 100
  variance_ne_zero := by norm_num

/-- A concrete open mass patch strictly inside the frozen support. -/
def unitPatch : Set Real := Ioo (9 / 10) (11 / 10)

theorem unit_mem_unitPatch : (1 : Real) ∈ unitPatch := by
  norm_num [unitPatch]

theorem unit_mem_massSupport_interior :
    (1 : Real) ∈ Ioo massLower massUpper := by
  norm_num [massLower, massUpper]

/-- The executable acceptance statement for the truncated-Gaussian mass law. -/
theorem problem_truncated_gaussian_mass_law :
    IsProbabilityMeasure (coordinateLaw parameters) ∧
      coordinateLaw parameters ≪ volume.restrict massSupport ∧
      volume.restrict massSupport ≪ coordinateLaw parameters ∧
      0 < coordinateLaw parameters unitPatch ∧
      0 < finiteLaw parameters 3
        {mass | ∀ i, mass i ∈ unitPatch} := by
  refine ⟨inferInstance,
    coordinateLaw_absolutelyContinuous_volume_restrict parameters,
    volume_restrict_absolutelyContinuous_coordinateLaw parameters, ?_, ?_⟩
  · exact coordinateLaw_pos_of_isOpen_of_mem_interior parameters
      isOpen_Ioo unit_mem_unitPatch unit_mem_massSupport_interior
  · apply finiteLaw_pos_of_isOpen_of_mem_interior parameters
      (x := fun _ ↦ 1)
    · rw [show {mass : Fin 3 → Real | ∀ i, mass i ∈ unitPatch} =
          Set.univ.pi (fun _ : Fin 3 ↦ unitPatch) by ext mass; simp]
      exact isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo
    · intro i
      exact unit_mem_unitPatch
    · intro i
      exact unit_mem_massSupport_interior

end GaussianMass

end

end ArchonPhysicsConsumers.Thermalization
