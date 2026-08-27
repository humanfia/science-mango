import ArchonPhysics.LennardJonesHamiltonianDuhamel

/-!
# Consumer: exact nonsingular Lennard--Jones modal Duhamel formula
-/

namespace ArchonPhysicsConsumers.Thermalization.LennardJonesHamiltonianDuhamel

open ArchonPhysics
open ArchonPhysics.BondPotentialHamiltonianPhyslib
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.LennardJonesHamiltonianDuhamel
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization

noncomputable section

/-- A five-site acceptance contract exercising the exact LJ force split,
mass-weighted random-mass mode projection, automatic finite-interval source
integrability, and interaction-picture Duhamel identity.  Nonsingularity is
supplied explicitly; the theorem does not assert collision avoidance or a
kinetic limit. -/
theorem fiveSite_exact_lennardJones_modal_duhamel
    (m : Lattice.PositiveMassConfig 5) (depth r₀ : Real)
    (k : Lattice.Site 5)
    (p q : Time → HilbertConfiguration 5)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m
      (LennardJonesPotential.bondPotential depth r₀) p q)
    (hnonsingular : ∀ t, LennardJonesBondsNonsingular r₀ (q t))
    (hdepth : 0 < depth) (hr₀ : r₀ ≠ 0)
    (hmode : 0 < modeFrequency m k) (t : Real) :
    phaseRenormalize (lennardJonesModeFrequency m depth r₀ k * t)
        (physlibModeAmplitude m depth r₀ k p q t) =
      physlibModeAmplitude m depth r₀ k p q 0 +
        ∫ s in 0..t, physlibModeRotatedSource m depth r₀ k q s := by
  exact interactionPicture_physlibMode_eq_initial_add_integral_of_nonsingular
    m depth r₀ k p q hp hq hHamilton hnonsingular
      (harmonicStiffness_pos hdepth hr₀).le
      (lennardJonesModeFrequency_pos m k hdepth hr₀ hmode) t

#print axioms fiveSite_exact_lennardJones_modal_duhamel

end

end ArchonPhysicsConsumers.Thermalization.LennardJonesHamiltonianDuhamel
