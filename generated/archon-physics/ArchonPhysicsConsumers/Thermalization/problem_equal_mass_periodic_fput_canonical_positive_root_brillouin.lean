import ArchonPhysics.EqualMassPeriodicFPUTCanonicalPositiveRootBrillouin

/-!
# Consumer endpoints for the canonical positive Umklapp root

These endpoints expose the exact lower- and upper-sum branch classification and
remove the two root-membership assumptions from the canonical collision
limit.  The remaining `data` object contains only the density, mark, and
support/measure hypotheses already required by the collision theorem.
-/

namespace ArchonPhysicsConsumers.Thermalization

open Set
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalPositiveRootBrillouin
open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTUmklappCollisionChartAdapter
open ArchonPhysics.EqualMassPeriodicFPUTUmklappFiniteAtlas
open ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian
open ArchonPhysics.NormalizedResonancePeakKernel
open Filter MeasureTheory Topology

noncomputable section

theorem equalMassPeriodicFPUT_positiveUmklappNumerator_consumer
    {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi) :
    0 < umklappResonanceNumerator k₀ k₁ :=
  umklappResonanceNumerator_pos_in_principal_zone
    hk₀0 hk₀2pi hk₁0 hk₁2pi

theorem equalMassPeriodicFPUT_positiveBranchOuterRegion_consumer
    {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi) :
    umklappPositiveArcsineBranch k₀ k₁ = .outer ↔
      k₀ + k₁ < 2 * Real.pi :=
  umklappPositiveArcsineBranch_eq_outer_iff_sum_lt_two_pi
    hk₀0 hk₀2pi hk₁0 hk₁2pi

theorem equalMassPeriodicFPUT_positiveBranchPrincipalRegion_consumer
    {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁) :
    umklappPositiveArcsineBranch k₀ k₁ = .principal ↔
      2 * Real.pi < k₀ + k₁ :=
  umklappPositiveArcsineBranch_eq_principal_iff_two_pi_lt_sum
    hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc

theorem equalMassPeriodicFPUT_positiveRootPrincipalZone_consumer
    {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁) :
    umklappArcsineRoot (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁ ∈
      Ioo 0 (2 * Real.pi) :=
  canonicalPositiveArcsineRoot_mem_principalZone
    hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc

theorem equalMassPeriodicFPUT_canonicalCollisionLimitNoRootBounds_consumer
    {k₀ k₁ : Real} {mark density : Real → Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (data : UmklappArcsineCollisionMeasureData
      (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁ mark density) :
    Tendsto
      (fun T : Real ↦ ∫ z in
        umklappArcsineLocalLeft (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁..
          umklappArcsineLocalRight
            (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁,
        normalizedFiniteTimeResonanceKernel
          (umklappReducedFourWaveMismatch k₀ k₁ z) T * mark z)
      atTop
      (nhds (mark (umklappArcsineRoot
          (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁) /
        (2 * Real.sqrt (umklappTransverseDiscriminant k₀ k₁)))) :=
  tendsto_canonicalPositiveUmklappCollisionChart_principalZone
    hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc data

#print axioms equalMassPeriodicFPUT_positiveUmklappNumerator_consumer
#print axioms equalMassPeriodicFPUT_positiveBranchOuterRegion_consumer
#print axioms equalMassPeriodicFPUT_positiveBranchPrincipalRegion_consumer
#print axioms equalMassPeriodicFPUT_positiveRootPrincipalZone_consumer
#print axioms equalMassPeriodicFPUT_canonicalCollisionLimitNoRootBounds_consumer

end

end ArchonPhysicsConsumers.Thermalization
