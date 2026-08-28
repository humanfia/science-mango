import ArchonPhysics.FPUTFractionalVolumeSchedule

/-!
# Consumer: fractional FPUT kinetic windows

This consumer selects the concrete nonempty exponent `b = 1/2`.  Its time
window diverges, remains negligible compared with volume, and therefore
converges to the actual rooted collision rate through the unconditional
bounded-variation diagonal.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTActualEffectiveDiagramEnumeration
open ArchonPhysics.EqualMassPeriodicFPUTActualFirstNormalForm
open ArchonPhysics.EqualMassPeriodicFPUTAlphaNTJointRemainder
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalPositiveRootBrillouin
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalUmklappCompactTest
open ArchonPhysics.EqualMassPeriodicFPUTExplicitCollisionKernelCertificate
open ArchonPhysics.EqualMassPeriodicFPUTLocalCollisionGridDiagonal
open ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian
open ArchonPhysics.FPUTFractionalVolumeSchedule
open Filter Topology

noncomputable section

theorem halfPower_mesoscopic_window_consumer :
    Tendsto (fractionalVolumePowerTime (1 / 2 : Real)) atTop atTop ∧
      Tendsto
        (fun n : Nat ↦
          fractionalVolumePowerTime (1 / 2 : Real) n / volumeScale n)
        atTop (nhds 0) :=
  ⟨halfPowerTime_tendsto_atTop,
    halfPowerTime_div_volume_tendsto_zero⟩

theorem concrete_fractional_monomial_tendsto_zero_consumer :
    Tendsto
      (fractionalScheduleMonomial (1 : Real) (1 / 2 : Real) 2 1 0)
      atTop (nhds 0) := by
  apply fractionalScheduleMonomial_tendsto_zero
  norm_num

theorem actualRooted_collision_halfPower_diagonal_consumer
    {N0 : Nat} [NeZero N0] (alpha : Real)
    (out : ActualInteractionBranchMode N0)
    (diagram : ActiveFeedbackEffectiveDiagramImage N0 out)
    (hdisc : 0 < umklappTransverseDiscriminant
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
    (ha0 : 0 ≤ canonicalDiagramLocalLeft diagram)
    (hb2pi : canonicalDiagramLocalRight diagram ≤ 2 * Real.pi) :
    Tendsto
      (fun n : Nat ↦
        localFourierGridCollisionQuadrature (n + 1)
          (canonicalDiagramUmklappMismatch diagram)
          (actualRootedLocalCollisionMark alpha out diagram)
          (canonicalDiagramLocalLeft diagram)
          (canonicalDiagramLocalRight diagram)
          (canonicalPositiveGeometry_principalZone
            (canonicalDiagramGridK₀_pos diagram)
            (canonicalDiagramGridK₀_lt_two_pi diagram)
            (canonicalDiagramGridK₁_pos diagram)
            (canonicalDiagramGridK₁_lt_two_pi diagram) hdisc).interval_lt.le
          (fractionalVolumePowerTime (1 / 2 : Real) n))
      atTop (nhds (actualRootedLocalCollisionRate alpha out diagram)) := by
  apply
    actualRootedLocalFourierGridCollision_tendsto_rate_fractionalSchedule
      alpha out diagram hdisc ha0 hb2pi
  · norm_num
  · norm_num

#print axioms halfPower_mesoscopic_window_consumer
#print axioms concrete_fractional_monomial_tendsto_zero_consumer
#print axioms actualRooted_collision_halfPower_diagonal_consumer

end

end ArchonPhysicsConsumers.Thermalization
