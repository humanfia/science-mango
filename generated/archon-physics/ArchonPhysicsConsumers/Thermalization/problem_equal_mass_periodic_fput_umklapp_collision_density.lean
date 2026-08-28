import ArchonPhysics.EqualMassPeriodicFPUTUmklappCollisionDensity

/-!
# Consumer: FPUT Umklapp collision-density limit
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTUmklappCollisionDensity
open ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian
open ArchonPhysics.NormalizedResonancePeakKernel
open Filter MeasureTheory Set Topology

noncomputable section

theorem equalMassPeriodicFPUT_positiveUmklapp_collision_limit_consumer
    {k₀ k₁ k₂ : Real} {mark density : Real → Real} {a b : Real}
    (chart : PositiveUmklappCollisionChart k₀ k₁ mark density a b)
    (hk₂ : k₂ ∈ uIcc a b)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (hresonant : umklappReducedFourWaveMismatch k₀ k₁ k₂ = 0) :
    Tendsto
      (fun T : Real ↦ ∫ x in a..b,
        normalizedFiniteTimeResonanceKernel
          (umklappReducedFourWaveMismatch k₀ k₁ x) T * mark x)
      atTop
      (nhds (mark k₂ /
        (2 * Real.sqrt (umklappTransverseDiscriminant k₀ k₁)))) :=
  tendsto_positiveUmklappCollisionChart_exactJacobian
    chart hk₂ hdisc hresonant

#print axioms equalMassPeriodicFPUT_positiveUmklapp_collision_limit_consumer

end

end ArchonPhysicsConsumers.Thermalization
