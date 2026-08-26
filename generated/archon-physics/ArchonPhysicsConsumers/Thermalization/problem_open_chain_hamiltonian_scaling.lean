import ArchonPhysics.OpenChainHamiltonianScaling

/-! Consumer: open-chain energy and cubic kinetic-time scaling. -/

namespace ArchonPhysicsConsumers.Thermalization.OpenChainHamiltonianScaling

open ArchonPhysics.HamiltonianScaling
open ArchonPhysics.OpenChainHamiltonianScaling

#check openForwardDifference_rescale
#check openLatticeHamiltonian_rescale
#check effectiveCoupling_cubic
#check effectiveCoupling_cubic_inv_sq
#check latticeHamiltonian_rescale

theorem problem_open_chain_cubic_inverse_energy_scaling
    (lambda epsilon : Real) (hepsilon : 0 < epsilon)
    (hlambda : lambda ≠ 0) :
    (effectiveCoupling lambda epsilon 3)⁻¹ ^ 2 =
      lambda⁻¹ ^ 2 * epsilon⁻¹ := by
  exact effectiveCoupling_cubic_inv_sq lambda epsilon hepsilon hlambda

#print axioms openLatticeHamiltonian_rescale
#print axioms effectiveCoupling_cubic_inv_sq
#print axioms problem_open_chain_cubic_inverse_energy_scaling

end ArchonPhysicsConsumers.Thermalization.OpenChainHamiltonianScaling
