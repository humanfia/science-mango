import ArchonPhysics.EqualMassPeriodicFPUTCanonicalUmklappCompactTest

/-!
# Consumer endpoints for compact canonical Umklapp tests

The first endpoint accepts the minimal continuous compact-test bundle.  The
second uses the explicit tent density and therefore has no measure-data input.
-/

namespace ArchonPhysicsConsumers.Thermalization

open Set
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalUmklappCompactTest
open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTUmklappCollisionChartAdapter
open ArchonPhysics.EqualMassPeriodicFPUTUmklappFiniteAtlas
open ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian
open ArchonPhysics.NormalizedResonancePeakKernel
open Filter MeasureTheory Topology

noncomputable section

theorem equalMassPeriodicFPUT_compactTestIntegrableLebesgue_consumer
    {rootBranch : UmklappArcsineBranch} {k₀ k₁ : Real}
    {density : Real → Real}
    (data : UmklappCompactTestDensityData rootBranch k₀ k₁ density) :
    Integrable density (volume : Measure Real) :=
  data.integrable_volume

theorem equalMassPeriodicFPUT_compactTestMeasureData_consumer
    {rootBranch : UmklappArcsineBranch} {k₀ k₁ : Real}
    {density : Real → Real}
    (data : UmklappCompactTestDensityData rootBranch k₀ k₁ density) :
    UmklappArcsineCollisionMeasureData rootBranch k₀ k₁
      (umklappDensityInducedMark k₀ k₁ density) density :=
  data.toCollisionMeasureData

theorem equalMassPeriodicFPUT_canonicalMismatchStraddlesZero_consumer
    {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁) :
    umklappReducedFourWaveMismatch k₀ k₁
        (umklappArcsineLocalLeft
          (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁) < 0 ∧
      0 < umklappReducedFourWaveMismatch k₀ k₁
        (umklappArcsineLocalRight
          (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁) :=
  canonicalPositiveMismatchImage_straddles_zero
    hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc

theorem equalMassPeriodicFPUT_compactTestCollision_consumer
    {k₀ k₁ : Real} {density : Real → Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (data : UmklappCompactTestDensityData
      (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁ density) :
    Tendsto
      (fun T : Real ↦ ∫ z in
        umklappArcsineLocalLeft
            (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁..
          umklappArcsineLocalRight
            (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁,
        normalizedFiniteTimeResonanceKernel
            (umklappReducedFourWaveMismatch k₀ k₁ z) T *
          umklappDensityInducedMark k₀ k₁ density z)
      atTop (nhds (density 0)) :=
  tendsto_canonicalPositiveUmklappCompactTest
    hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc data

theorem equalMassPeriodicFPUT_explicitTentCollision_consumer
    {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁) :
    Tendsto
      (fun T : Real ↦ ∫ z in
        umklappArcsineLocalLeft
            (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁..
          umklappArcsineLocalRight
            (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁,
        normalizedFiniteTimeResonanceKernel
            (umklappReducedFourWaveMismatch k₀ k₁ z) T *
          canonicalPositiveUmklappTentMark k₀ k₁ z)
      atTop (nhds (canonicalPositiveUmklappTentDensity k₀ k₁ 0)) :=
  tendsto_canonicalPositiveUmklappTentCollision
    hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc

#print axioms equalMassPeriodicFPUT_compactTestIntegrableLebesgue_consumer
#print axioms equalMassPeriodicFPUT_compactTestMeasureData_consumer
#print axioms equalMassPeriodicFPUT_canonicalMismatchStraddlesZero_consumer
#print axioms equalMassPeriodicFPUT_compactTestCollision_consumer
#print axioms equalMassPeriodicFPUT_explicitTentCollision_consumer

end

end ArchonPhysicsConsumers.Thermalization
