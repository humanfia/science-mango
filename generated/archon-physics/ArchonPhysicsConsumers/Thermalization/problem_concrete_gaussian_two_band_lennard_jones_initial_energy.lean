import ArchonPhysics.ConcreteGaussianTwoBandLennardJonesInitialEnergy

/-!
# Consumer: exact LJ energy of the concrete Gaussian two-band initial state

This five-site acceptance target fixes the prescribed harmonic energy density
to `2/5`, the LJ equilibrium distance to one, and the well depth to `1/72`,
so the LJ harmonic stiffness is exactly one.  Conditional on simple spectrum
and the explicit initial bond tube `|Delta q_i| <= 1/40`, it checks:

* harmonic total energy is exactly `5 * (2/5)`;
* exact LJ total energy differs by less than `1/3200`; and
* exact LJ energy density differs from the parameter `2/5` by less than
  `1/16000`.

The error contains the honest cubic and quartic LJ anharmonic terms plus the
exact fifth-order LJ/FPUT remainder.  The tube remains an explicit premise.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ConcreteGaussianTwoBandInitialEnsemble
open ArchonPhysics.ConcreteGaussianTwoBandPhysicalInitialData
open ArchonPhysics.ConcreteGaussianTwoBandLennardJonesInitialEnergy
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhysicalHarmonicEnergyIdentity

noncomputable section

namespace ConcreteGaussianTwoBandLennardJonesInitialEnergy

def energyDensity : Real := 2 / 5

/-- Kernel-checked concrete exact-LJ initial-energy comparison. -/
theorem problem_concrete_gaussian_two_band_lennard_jones_initial_energy :
    forall (sample : SampleSpace),
      SimpleOrderedSpectrum
        (harmonicHermitian (massSample (N := 5) sample)) ->
      (forall i : Lattice.Site 5,
        |Lattice.forwardDifference
          (asConfiguration
            (initialPhysicalPosition energyDensity sample)) i| <= 1 / 40) ->
      physicalHarmonicHamiltonian (massSample (N := 5) sample)
          (asConfiguration (initialPhysicalMomentum energyDensity sample))
          (asConfiguration (initialPhysicalPosition energyDensity sample)) =
        5 * energyDensity ∧
      |exactLJInitialHamiltonian (N := 5) 1 energyDensity sample -
          5 * energyDensity| < 1 / 3200 ∧
      |exactLJInitialEnergyDensity (N := 5) 1 energyDensity sample -
          energyDensity| < 1 / 16000 := by
  intro sample hsimple htube
  have hharmonic := physicalHarmonicHamiltonian_initial_eq_total
    (N := 5) (energyDensity := energyDensity) (by norm_num) (by norm_num [energyDensity]) sample hsimple
  have htotal := abs_exactLJInitialHamiltonian_sub_prescribedTotal_le
    (N := 5) (energyDensity := energyDensity) (by norm_num) (by norm_num [energyDensity]) sample hsimple
    (r0 := 1) (rho := 1 / 40) (amplitude := 1 / 40)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa using htube) htube
  have hdensity := abs_exactLJInitialEnergyDensity_sub_parameter_le
    (N := 5) (energyDensity := energyDensity) (by norm_num) (by norm_num [energyDensity]) sample hsimple
    (r0 := 1) (rho := 1 / 40) (amplitude := 1 / 40)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa using htube) htube
  have hperBond := harmonicComparisonPerBondBound_one_div_forty_lt
  refine ⟨hharmonic, ?_, hdensity.trans_lt hperBond⟩
  nlinarith

#print axioms problem_concrete_gaussian_two_band_lennard_jones_initial_energy
#print axioms abs_bondPotential_sub_unitHarmonic_le
#print axioms abs_exactLJInitialEnergyDensity_sub_parameter_le

end ConcreteGaussianTwoBandLennardJonesInitialEnergy

end

end ArchonPhysicsConsumers.Thermalization
