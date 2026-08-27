import ArchonPhysics.LennardJonesForceTaylorLattice

/-!
# Consumer checks for finite-volume Lennard--Jones force Taylor control

The contracts below expose the empirical-moment and volume-independent tube
bounds. Both are static estimates at one instant; neither claims trajectory
persistence or a kinetic-time accumulated-error estimate.
-/

namespace ArchonPhysicsConsumers.Thermalization.LennardJonesForceTaylorLattice

open ArchonPhysics
open ArchonPhysics.BondPotentialHamiltonianPhyslib
open ArchonPhysics.LennardJonesForceTaylorTube
open ArchonPhysics.LennardJonesForceTaylorLattice

noncomputable section

theorem empirical_fourth_moment_contract
    {N : Nat} [NeZero N]
    {depth r₀ rho : Real} (strain : Lattice.Site N → Real)
    (hdepth : 0 ≤ depth) (hr₀ : 0 < r₀)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (htube : ∀ i, |strain i| ≤ rho * r₀) :
    perSiteAbsoluteForceRemainder depth r₀ strain ≤
      depth / r₀ * forceRemainderTubeConstant rho *
        empiricalRelativeFourthStrainMoment r₀ strain :=
  perSiteAbsoluteForceRemainder_le_fourthMoment
    strain hdepth hr₀ hrho0 hrho1 htube

theorem uniform_tube_power_contract
    {N : Nat} [NeZero N]
    {depth r₀ rho : Real} (strain : Lattice.Site N → Real)
    (hdepth : 0 ≤ depth) (hr₀ : 0 < r₀)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (htube : ∀ i, |strain i| ≤ rho * r₀) :
    perSiteAbsoluteForceRemainder depth r₀ strain ≤
      depth / r₀ * forceRemainderTubeConstant rho * rho ^ 4 :=
  perSiteAbsoluteForceRemainder_le_tubePower
    strain hdepth hr₀ hrho0 hrho1 htube

#check perSiteAbsoluteForceRemainder_le_fourthMoment
#check perSiteAbsoluteForceRemainder_le_tubePower

#print axioms empirical_fourth_moment_contract
#print axioms uniform_tube_power_contract

end

end ArchonPhysicsConsumers.Thermalization.LennardJonesForceTaylorLattice
