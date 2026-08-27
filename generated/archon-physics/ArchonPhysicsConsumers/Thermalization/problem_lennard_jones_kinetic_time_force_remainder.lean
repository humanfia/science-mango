import ArchonPhysics.LennardJonesKineticTimeForceRemainder

/-!
# Consumer: the LJ/FPUT force discrepancy is small on kinetic time
-/

namespace ArchonPhysicsConsumers.Thermalization.LennardJonesKineticTimeForceRemainder

open Set
open ArchonPhysics.LennardJonesKineticTimeForceRemainder
open ArchonPhysics.LennardJonesNormalizedForceScaling

noncomputable section

theorem kinetic_time_force_remainder_contract
    {depth r₀ g rho L amplitudeBound : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) (hg : 0 < g)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hL : 0 ≤ L) (hAmplitude : 0 ≤ amplitudeBound)
    (amplitude : Real → Real)
    (hIntegrable : IntervalIntegrable
      (fun t => normalizedForceRemainder depth r₀ g (amplitude t))
      MeasureTheory.volume 0 (kineticWindowTime g L))
    (htube : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      |g * amplitude t| ≤ rho * r₀)
    (hamplitude : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      |amplitude t| ≤ amplitudeBound) :
    ‖∫ t in 0..kineticWindowTime g L,
        normalizedForceRemainder depth r₀ g (amplitude t)‖ ≤
      kineticForceRemainderCoefficient r₀ rho amplitudeBound * L * g := by
  exact (intervalIntegrable_and_norm_integral_forceRemainder_le_kinetic
    hdepth hr₀ hg hrho0 hrho1 hL hAmplitude amplitude hIntegrable
      htube hamplitude).2

#print axioms kinetic_time_force_remainder_contract
#print axioms kinetic_integrated_force_bound_tendsto_zero

end

end ArchonPhysicsConsumers.Thermalization.LennardJonesKineticTimeForceRemainder
