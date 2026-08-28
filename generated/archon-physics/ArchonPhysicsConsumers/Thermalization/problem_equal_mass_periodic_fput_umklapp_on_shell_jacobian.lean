import ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian

/-!
# Consumer: exact equal-mass FPUT Umklapp on-shell Jacobian
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTUmklappTransversality
open ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian

noncomputable section

theorem equalMassPeriodicFPUT_umklapp_onShell_Jacobian_consumer
    {k₀ k₁ k₂ : Real}
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (hresonant : umklappReducedFourWaveMismatch k₀ k₁ k₂ = 0) :
    |umklappK₂DerivativeFactor k₀ k₁ k₂| =
      2 * Real.sqrt (umklappTransverseDiscriminant k₀ k₁) :=
  abs_umklappK₂DerivativeFactor_of_resonant hdisc hresonant

#print axioms equalMassPeriodicFPUT_umklapp_onShell_Jacobian_consumer

end


end ArchonPhysicsConsumers.Thermalization
