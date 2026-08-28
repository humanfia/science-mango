import ArchonPhysics.EqualMassPeriodicFPUTLocalCollisionGridDiagonal

/-!
# Consumer endpoints for the local Fourier-grid collision diagonal

The principal endpoint is a correctly normalized `2π/N` Fourier sum for the
actual rooted coefficient and explicit tent mark.  The unconditional
quadrature route uses `T_N²/N → 0`; a named linear-time certificate exposes
the sole extra estimate needed for the sharper `T_N/N → 0` window.
-/

namespace ArchonPhysicsConsumers.Thermalization

open Set
open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTActualEffectiveDiagramEnumeration
open ArchonPhysics.EqualMassPeriodicFPUTActualFirstNormalForm
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalPositiveRootBrillouin
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalUmklappCompactTest
open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTExplicitCollisionKernelCertificate
open ArchonPhysics.EqualMassPeriodicFPUTLocalCollisionGridDiagonal
open ArchonPhysics.EqualMassPeriodicFPUTUmklappCollisionChartAdapter
open ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian
open ArchonPhysics.EqualMassPeriodicFPUTUmklappTransversality
open ArchonPhysics.FPUTFiniteTimeCollisionQuadrature
open ArchonPhysics.Lattice
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.TransverseResonanceChartApproximateIdentity
open Filter MeasureTheory Topology

noncomputable section

theorem equalMassPeriodicFPUT_actualRootedTentRegularity_consumer
    {N : Nat} [NeZero N] (alpha : Real)
    (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out)
    (hdisc : 0 < umklappTransverseDiscriminant
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)) :
    Nonempty (ActualRootedLocalMarkRegularity alpha out diagram) :=
  exists_actualRootedLocalMarkRegularity alpha out diagram hdisc

theorem equalMassPeriodicFPUT_actualRootedLocalGridDiagonal_consumer
    {N₀ : Nat} [NeZero N₀] (alpha : Real)
    (out : ActualInteractionBranchMode N₀)
    (diagram : ActiveFeedbackEffectiveDiagramImage N₀ out)
    (hdisc : 0 < umklappTransverseDiscriminant
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
    (ha0 : 0 ≤ canonicalDiagramLocalLeft diagram)
    (hb2pi : canonicalDiagramLocalRight diagram ≤ 2 * Real.pi)
    (time : Nat → Real) (htimePos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (hlinear : Tendsto
      (fun n : Nat ↦ time n / (((n + 1 : Nat) : Real)))
      atTop (nhds 0))
    (hquadratic : Tendsto
      (fun n : Nat ↦ (time n) ^ 2 / (((n + 1 : Nat) : Real)))
      atTop (nhds 0)) :
    Tendsto
      (fun n : Nat ↦
        localFourierGridCollisionQuadrature (n + 1)
          (fun z ↦ umklappReducedFourWaveMismatch
            (canonicalDiagramGridK₀ diagram)
            (canonicalDiagramGridK₁ diagram) z)
          (umklappDensityInducedMark
            (canonicalDiagramGridK₀ diagram)
            (canonicalDiagramGridK₁ diagram)
            (actualRootedLocalCollisionDensity alpha out diagram))
          (umklappArcsineLocalLeft
            (umklappPositiveArcsineBranch
              (canonicalDiagramGridK₀ diagram)
              (canonicalDiagramGridK₁ diagram))
            (canonicalDiagramGridK₀ diagram)
            (canonicalDiagramGridK₁ diagram))
          (umklappArcsineLocalRight
            (umklappPositiveArcsineBranch
              (canonicalDiagramGridK₀ diagram)
              (canonicalDiagramGridK₁ diagram))
            (canonicalDiagramGridK₀ diagram)
            (canonicalDiagramGridK₁ diagram))
          (canonicalPositiveGeometry_principalZone
            (canonicalDiagramGridK₀_pos diagram)
            (canonicalDiagramGridK₀_lt_two_pi diagram)
            (canonicalDiagramGridK₁_pos diagram)
            (canonicalDiagramGridK₁_lt_two_pi diagram) hdisc).interval_lt.le
          (time n))
      atTop (nhds (actualRootedLocalCollisionRate alpha out diagram)) :=
  actualRootedLocalFourierGridCollision_tendsto_rate_of_time_sq
    alpha out diagram hdisc ha0 hb2pi time htimePos htime
      hlinear hquadratic

theorem equalMassPeriodicFPUT_linearTimeGridAdapter_consumer
    {mismatch mismatchDerivative mark density : Real → Real}
    {a b : Real}
    (chart : TransverseResonanceChart
      mismatch mismatchDerivative mark density a b)
    (hab : a ≤ b)
    (certificate : LinearTimeLocalCollisionQuadratureCertificate
      mismatch mark a b hab)
    (time : Nat → Real) (htimePos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (hlinear : Tendsto
      (fun n : Nat ↦ time n / (((n + 1 : Nat) : Real)))
      atTop (nhds 0)) :
    Tendsto
      (fun n : Nat ↦
        localFourierGridCollisionQuadrature (n + 1)
          mismatch mark a b hab (time n))
      atTop (nhds (density 0)) :=
  localFourierGridCollisionQuadrature_tendsto_density_zero_of_linearTime
    chart hab certificate time htimePos htime hlinear

theorem equalMassPeriodicFPUT_actualRootedLocalRatePositive_consumer
    {N : Nat} [NeZero N] {alpha : Real} (halpha : alpha ≠ 0)
    (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out)
    (hdisc : 0 < umklappTransverseDiscriminant
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)) :
    0 < actualRootedLocalCollisionRate alpha out diagram :=
  actualRootedLocalFourierGridCollision_rate_pos
    halpha out diagram hdisc

#print axioms equalMassPeriodicFPUT_actualRootedTentRegularity_consumer
#print axioms equalMassPeriodicFPUT_actualRootedLocalGridDiagonal_consumer
#print axioms equalMassPeriodicFPUT_linearTimeGridAdapter_consumer
#print axioms equalMassPeriodicFPUT_actualRootedLocalRatePositive_consumer

end

end ArchonPhysicsConsumers.Thermalization
