import ArchonPhysics.TruncatedGaussianIIDMassSequence

/-!
# Acceptance target: an infinite iid positive truncated-Gaussian mass sequence

The concrete law below is centered at unit mass with variance `1 / 100` before
conditioning on `[4/5,6/5]`.  The target checks exact one-coordinate laws,
independence, simultaneous almost-sure raw support, and the pointwise support
and positivity of the clipped representative.
-/

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory ProbabilityTheory
open ArchonPhysics TruncatedGaussianMassLaw

noncomputable section

namespace GaussianIIDMass

open TruncatedGaussianIIDMassSequence

/-- Concrete nondegenerate Gaussian parameters for the iid product. -/
def parameters : Parameters where
  mean := 1
  variance := 1 / 100
  variance_ne_zero := by norm_num

/-- Executable acceptance statement for the countable product construction. -/
theorem problem_truncated_gaussian_iid_mass_sequence :
    IsProbabilityMeasure (probability parameters) ∧
      (∀ n, HasLaw (rawMassAt n) (coordinateLaw parameters)
        (probability parameters)) ∧
      iIndepFun rawMassAt (probability parameters) ∧
      (∀ᵐ sample ∂probability parameters,
        ∀ n, rawMassAt n sample ∈ RandomEnsemble.massSupport) ∧
      (∀ n, HasLaw (massAt n) (coordinateLaw parameters)
        (probability parameters)) ∧
      iIndepFun massAt (probability parameters) ∧
      (∀ n sample, massAt n sample ∈ RandomEnsemble.massSupport ∧ 0 < massAt n sample) := by
  refine ⟨inferInstance, rawMassAt_hasLaw parameters,
    rawMassCoordinates_iIndep parameters,
    rawMassSequence_mem_support_ae parameters,
    massAt_hasLaw parameters, massCoordinates_iIndep parameters, ?_⟩
  intro n sample
  exact ⟨massAt_mem_support n sample, massAt_pos n sample⟩

end GaussianIIDMass

end

end ArchonPhysicsConsumers.Thermalization
