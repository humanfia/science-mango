import ArchonPhysics.PhyslibFPUTEnergyShellFlowLipschitz

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalRandomMassGlobalFlow
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.PhyslibFPUTEnergyShellFlowLipschitz

noncomputable section

variable {N : Nat} [NeZero N]

/-- Consumer-facing check: a common energy-shell cutoff gives a fixed-time
Gronwall-Lipschitz bound for the actual FPUT flow selected on that shell. -/
example (shell : UniformRandomMassEnergyShell N) (t : Real) :
    LipschitzWith (energyShellFlowAmplification shell t)
      (fun x : ParametricPhaseSpace N ↦
        canonicalRandomMassGlobalFlow shell (x, t)) :=
  canonicalRandomMassGlobalFlow_lipschitz_fixedTime shell t

#print axioms canonicalRandomMassGlobalFlow_lipschitz_fixedTime

end


end ArchonPhysicsConsumers.Thermalization
