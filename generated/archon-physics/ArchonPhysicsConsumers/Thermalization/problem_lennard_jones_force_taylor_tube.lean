import ArchonPhysics.LennardJonesForceTaylorTube

/-!
# Consumer: quantitative force-level LJ/FPUT comparison
-/

namespace ArchonPhysicsConsumers.Thermalization.LennardJonesForceTaylorTube

open ArchonPhysics.LennardJonesForceTaylorTube
open ArchonPhysics.BondPotentialHamiltonianPhyslib

noncomputable section

/-- On a relative strain tube, the exact LJ force differs from its local
FPUT alpha-beta force by a rigorously fourth-order term. -/
theorem force_remainder_contract
    {depth r₀ rho x : Real}
    (hdepth : 0 ≤ depth) (hr₀ : 0 < r₀)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hx : |x| ≤ rho * r₀) :
    |lennardJonesDerivative depth r₀ x -
        localAlphaBetaForce depth r₀ x| ≤
      depth / r₀ * forceRemainderTubeConstant rho *
        (|x| / r₀) ^ 4 := by
  exact abs_lennardJonesDerivative_sub_localAlphaBetaForce_le
    hdepth hr₀ hrho0 hrho1 hx

#print axioms force_remainder_contract

end

end ArchonPhysicsConsumers.Thermalization.LennardJonesForceTaylorTube
