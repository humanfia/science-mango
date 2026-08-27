import ArchonPhysics.LennardJonesModalRemainderMeanSquareBound

/-!
# Consumer: volume-uniform mean-square LJ modal remainder
-/

namespace ArchonPhysicsConsumers.Thermalization.LennardJonesModalRemainderMeanSquareBound

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.LennardJonesKineticTimeForceRemainder
open ArchonPhysics.LennardJonesModalRemainderMeanSquareBound

noncomputable section

/-- For the paper mass support `[4/5, 6/5]`, the all-mode mean-square
coefficient is the explicit volume-independent constant five. -/
theorem paperMassSupport_modalHigherResidualMeanSquare_le_g_six
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hmass : ∀ i, (4 / 5 : Real) ≤ m.mass i)
    {depth r₀ g rho amplitudeBound : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) (hg : 0 < g)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hAmplitude : 0 ≤ amplitudeBound)
    (q : HilbertConfiguration N)
    (htube : ∀ i : Lattice.Site N,
      |g * Lattice.forwardDifference (asConfiguration q) i| ≤ rho * r₀)
    (hamplitude : ∀ i : Lattice.Site N,
      |Lattice.forwardDifference (asConfiguration q) i| ≤ amplitudeBound) :
    modalHigherResidualMeanSquare m depth r₀ g q ≤
      5 * kineticForceRemainderCoefficient r₀ rho amplitudeBound ^ 2 * g ^ 6 := by
  have h := modalHigherResidualMeanSquare_le_g_six
    m (4 / 5 : Real) (by norm_num) hmass
      hdepth hr₀ hg hrho0 hrho1 hAmplitude q htube hamplitude
  norm_num at h ⊢
  exact h

#print axioms paperMassSupport_modalHigherResidualMeanSquare_le_g_six
#print axioms sum_sq_normalizedHigherResidualModalForce_le_bond_sum_sq
#print axioms modalHigherResidualMeanSquare_le_g_six

end

end ArchonPhysicsConsumers.Thermalization.LennardJonesModalRemainderMeanSquareBound
