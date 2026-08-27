import ArchonPhysics.ConcreteGaussianTwoBandPhysicalInitialData

/-!
# Consumer: physical data for the concrete Gaussian two-band ensemble

This five-site target fixes energy density `2/5` and checks that the concrete
Gaussian-mass / Haar-phase modal ensemble produces globally measurable
physical position and canonical momentum.  The mass transforms recover the
assembled modal coordinates pointwise, while almost-sure Gaussian simple
spectrum gives every prescribed modal energy, total energy `5 * (2/5)`, and
the same value for the original-coordinate harmonic Hamiltonian.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ConcreteGaussianTwoBandInitialEnsemble
open ArchonPhysics.ConcreteGaussianTwoBandPhysicalInitialData
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.PhysicalHarmonicEnergyIdentity
open ArchonPhysics.RandomMassMeasurableHarmonicEnergy
open MeasureTheory
open scoped BigOperators

noncomputable section

namespace ConcreteGaussianTwoBandPhysicalInitialData

def energyDensity : Real := 2 / 5

/-- Kernel-checked acceptance contract for the concrete physical initial
state. -/
theorem problem_concrete_gaussian_two_band_physical_initial_data :
    Measurable (initialPhysicalPosition (N := 5) energyDensity) ∧
    Measurable (initialPhysicalMomentum (N := 5) energyDensity) ∧
    (forall sample : SampleSpace,
      sqrtMassTransform (massSample (N := 5) sample)
          (initialPhysicalPosition energyDensity sample) =
        WithLp.toLp 2
          (initialMassWeightedPosition energyDensity sample) ∧
      inverseSqrtMassTransform (massSample (N := 5) sample)
          (initialPhysicalMomentum energyDensity sample) =
        WithLp.toLp 2
          (initialMassWeightedMomentum energyDensity sample)) ∧
    ∀ᵐ sample ∂concreteEnsemble.probability,
      (forall mode : OrderedMode 5,
        harmonicOrderedPhysicalModeEnergy massSample
            (initialPhysicalPosition energyDensity)
            (initialPhysicalMomentum energyDensity) sample mode =
          orderedModalEnergy 5 energyDensity mode) ∧
      (∑ mode : OrderedMode 5,
        harmonicOrderedPhysicalModeEnergy massSample
          (initialPhysicalPosition energyDensity)
          (initialPhysicalMomentum energyDensity) sample mode) =
        5 * energyDensity ∧
      physicalHarmonicHamiltonian (massSample (N := 5) sample)
          (CoerciveHamiltonianPhyslib.asConfiguration
            (initialPhysicalMomentum energyDensity sample))
          (CoerciveHamiltonianPhyslib.asConfiguration
            (initialPhysicalPosition energyDensity sample)) =
        5 * energyDensity := by
  refine ⟨measurable_initialPhysicalPosition energyDensity,
    measurable_initialPhysicalMomentum energyDensity, ?_, ?_⟩
  · intro sample
    exact ⟨sqrtMassTransform_initialPhysicalPosition energyDensity sample,
      inverseSqrtMassTransform_initialPhysicalMomentum energyDensity sample⟩
  · exact physicalInitialData_energy_spec_ae (N := 5) (by norm_num)
      (by norm_num [energyDensity])

#print axioms problem_concrete_gaussian_two_band_physical_initial_data
#print axioms measurable_initialPhysicalPosition
#print axioms physicalOrderedModeEnergy_initial_eq_prescribed
#print axioms physicalInitialData_energy_spec_ae

end ConcreteGaussianTwoBandPhysicalInitialData

end

end ArchonPhysicsConsumers.Thermalization
