import ArchonPhysics.LennardJonesEnergyConservedTubeFlow

/-!
# Consumer: energy-conserved invariant tubes for exact Lennard--Jones flow
-/

namespace ArchonPhysicsConsumers.Thermalization.LennardJonesEnergyConservedTubeFlow

open ArchonPhysics
open ArchonPhysics.BondPotentialHamiltonianPhyslib
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.LennardJonesEnergyConservedTubeFlow
open ArchonPhysics.LennardJonesHamiltonianDuhamel
open ArchonPhysics.LennardJonesPotential
open ArchonPhysics.LennardJonesThermodynamicThreshold
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization

noncomputable section

/-- Five-site acceptance contract: autonomous Hamilton equations, an initial
strict tube, and initial *total* energy below the one-bond barrier imply an
all-time tube, exact energy conservation, automatic bond nonsingularity, and
the finite-time exact modal Duhamel identity. -/
theorem fiveSite_exact_lennardJones_energy_conserved_tube_flow
    (m : Lattice.PositiveMassConfig 5) (depth r₀ rho : Real)
    (k : Lattice.Site 5)
    (p q : Time → HilbertConfiguration 5)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m
      (LennardJonesPotential.bondPotential depth r₀) p q)
    (hdepth : 0 < depth) (hr₀ : 0 < r₀)
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (hinitialTube : UniformRelativeTube r₀ rho (asConfiguration (q 0)))
    (hinitialEnergy : periodicRandomMassHamiltonian m depth r₀
      (asConfiguration (p 0)) (asConfiguration (q 0)) <
        relativeTubeBarrier depth rho)
    (hmode : 0 < modeFrequency m k) (tau : Real) :
    (∀ t : Time, UniformRelativeTube r₀ rho (asConfiguration (q t))) ∧
    (∀ t : Time,
      periodicRandomMassHamiltonian m depth r₀
          (asConfiguration (p t)) (asConfiguration (q t)) =
        periodicRandomMassHamiltonian m depth r₀
          (asConfiguration (p 0)) (asConfiguration (q 0))) ∧
    (∀ t : Time, LennardJonesBondsNonsingular r₀ (q t)) ∧
    phaseRenormalize (lennardJonesModeFrequency m depth r₀ k * tau)
        (physlibModeAmplitude m depth r₀ k p q tau) =
      physlibModeAmplitude m depth r₀ k p q 0 +
        ∫ s in 0..tau, physlibModeRotatedSource m depth r₀ k q s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact uniformRelativeTube_all_time_of_initial_energy_lt_barrier
      m depth r₀ rho p q hdepth.le hr₀ hrho.le hrhoOne hp hq hHamilton
        hinitialTube hinitialEnergy
  · intro t
    exact periodicRandomMassHamiltonian_conserved_of_initial_energy_lt_barrier
      m depth r₀ rho p q hdepth.le hr₀ hrho.le hrhoOne hp hq hHamilton
        hinitialTube hinitialEnergy t
  · exact lennardJonesBondsNonsingular_all_time_of_initial_energy_lt_barrier
      m depth r₀ rho p q hdepth.le hr₀ hrho.le hrhoOne hp hq hHamilton
        hinitialTube hinitialEnergy
  · exact interactionPicture_physlibMode_eq_initial_add_integral_of_energyTube
      m depth r₀ rho k p q hdepth.le hr₀ hrho.le hrhoOne hp hq hHamilton
        hinitialTube hinitialEnergy
        (lennardJonesModeFrequency_pos m k hdepth hr₀.ne' hmode) tau

#print axioms fiveSite_exact_lennardJones_energy_conserved_tube_flow

end

end ArchonPhysicsConsumers.Thermalization.LennardJonesEnergyConservedTubeFlow
