import ArchonPhysics.LennardJonesEnergyDensityTubeCounterexample

/-!
# Consumer: a genuine thermodynamic LJ density/tube counterexample

This endpoint locks the explicit cofinal family `N = n + 2`.  At zero
momentum and unit masses its Hamiltonian density converges below any prescribed
positive target, while the configuration stays LJ-admissible and eventually
violates every fixed all-bond relative-strain tube.
-/

namespace ArchonPhysicsConsumers.Thermalization.LennardJonesEnergyDensityTubeCounterexample

open ArchonPhysics
open ArchonPhysics.LennardJonesPotential
open ArchonPhysics.LennardJonesThermodynamicThreshold
open ArchonPhysics.LennardJonesEnergyDensityTubeCounterexample
open Filter
open scoped Topology

noncomputable section

/-- No positive, volume-independent mean-energy cutoff can force all LJ bonds
to remain in a fixed Taylor tube in the thermodynamic limit. -/
theorem lj_positive_energyDensity_does_not_force_uniformRelativeTube
    {depth r₀ ρ e : Real} (hr₀ : 0 < r₀) (he : 0 < e) :
    ∃ b : Real,
      0 < b ∧ b < r₀ ∧
      Tendsto
        (fun n : Nat =>
          periodicEnergyDensity (unitPositiveMassConfig (n + 2)) depth r₀
            (zeroMomentum (n + 2))
            (singleTensileDefectConfiguration n b))
        atTop (𝓝 (bondPotential depth r₀ (-b))) ∧
      bondPotential depth r₀ (-b) < e ∧
      ∀ᶠ n : Nat in atTop,
        AdmissibleConfiguration r₀
            (singleTensileDefectConfiguration n b) ∧
          periodicEnergyDensity (unitPositiveMassConfig (n + 2)) depth r₀
              (zeroMomentum (n + 2))
              (singleTensileDefectConfiguration n b) < e ∧
          ¬ UniformRelativeTube r₀ ρ
              (singleTensileDefectConfiguration n b) := by
  exact eventually_admissible_lowEnergyDensity_not_uniformRelativeTube hr₀ he

#check forwardDifference_singleTensileDefectConfiguration
#check periodicPotentialEnergy_singleTensileDefectConfiguration
#check singleTensileDefectConfiguration_admissible
#check tendsto_defectHamiltonianEnergyDensity
#check eventually_admissible_lowEnergyDensity_not_uniformRelativeTube

#print axioms lj_positive_energyDensity_does_not_force_uniformRelativeTube

end

end ArchonPhysicsConsumers.Thermalization.LennardJonesEnergyDensityTubeCounterexample
