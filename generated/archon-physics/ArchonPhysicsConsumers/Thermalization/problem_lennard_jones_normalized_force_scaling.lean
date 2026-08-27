import ArchonPhysics.LennardJonesNormalizedForceScaling

/-!
# Consumer: normalized exact LJ force has a cubic weak-coupling remainder
-/

namespace ArchonPhysicsConsumers.Thermalization.LennardJonesNormalizedForceScaling

open ArchonPhysics.LennardJonesNormalizedForceScaling
open ArchonPhysics.LennardJonesForceTaylorTube

noncomputable section

theorem normalized_force_remainder_contract
    {depth r₀ g rho x : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) (hg : g ≠ 0)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (htube : |g * x| ≤ rho * r₀) :
    |normalizedForceRemainder depth r₀ g x| ≤
      r₀ / 72 * forceRemainderTubeConstant rho * |g| ^ 3 *
        (|x| / r₀) ^ 4 := by
  exact abs_normalizedForceRemainder_le_g_cubed
    hdepth hr₀ hg hrho0 hrho1 htube

#print axioms normalized_force_remainder_contract

end

end ArchonPhysicsConsumers.Thermalization.LennardJonesNormalizedForceScaling
