import ArchonPhysics.LennardJonesModalRemainderKineticBound

/-!
# Consumer: finite-mode LJ higher remainder is small on kinetic time
-/

namespace ArchonPhysicsConsumers.Thermalization.LennardJonesModalRemainderKineticBound

open Set
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.LennardJonesKineticTimeForceRemainder
open ArchonPhysics.LennardJonesModalRemainderKineticBound

noncomputable section

theorem fiveSite_modal_remainder_contract
    (m : Lattice.PositiveMassConfig 5) (k : Lattice.Site 5)
    {depth r₀ g rho L amplitudeBound : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) (hg : 0 < g)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hL : 0 ≤ L) (hAmplitude : 0 ≤ amplitudeBound)
    (q : Real → HilbertConfiguration 5)
    (hIntegrable : IntervalIntegrable
      (fun t => normalizedHigherResidualModalForce
        m depth r₀ g (q t) k)
      MeasureTheory.volume 0 (kineticWindowTime g L))
    (htube : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      ∀ i : Lattice.Site 5,
        |g * Lattice.forwardDifference (asConfiguration (q t)) i| ≤ rho * r₀)
    (hamplitude : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      ∀ i : Lattice.Site 5,
        |Lattice.forwardDifference (asConfiguration (q t)) i| ≤ amplitudeBound) :
    ‖∫ t in 0..kineticWindowTime g L,
        normalizedHigherResidualModalForce m depth r₀ g (q t) k‖ ≤
      modalHigherRemainderCoefficient m k r₀ rho amplitudeBound * L * g := by
  exact (intervalIntegrable_and_norm_integral_modalHigherResidual_le_kinetic
    m k hdepth hr₀ hg hrho0 hrho1 hL hAmplitude q hIntegrable
      htube hamplitude).2

#print axioms fiveSite_modal_remainder_contract
#print axioms modalCoordinates_transformedNormalizedHigherResidualForce

end

end ArchonPhysicsConsumers.Thermalization.LennardJonesModalRemainderKineticBound
