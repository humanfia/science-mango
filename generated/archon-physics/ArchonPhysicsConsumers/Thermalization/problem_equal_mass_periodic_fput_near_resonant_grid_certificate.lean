import ArchonPhysics.EqualMassPeriodicFPUTNearResonantGridCertificate

/-!
# Consumer endpoints for the near-resonant Fourier-grid certificate

The canonical positive Umklapp root is approximated by one explicit periodic
grid mode.  The endpoints below expose its `O(1/N)` angle and energy errors,
the resulting local collision certificate, and the joint `T_N/N → 0` sinc
window.  They do not assert a global kinetic or Riemann-sum limit.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTActualEffectiveDiagramEnumeration
open ArchonPhysics.EqualMassPeriodicFPUTActualFirstNormalForm
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalPositiveRootBrillouin
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalTwoToTwoShell
open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTDirectSectorClosure
open ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
open ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
open ArchonPhysics.EqualMassPeriodicFPUTExplicitCollisionKernelCertificate
open ArchonPhysics.EqualMassPeriodicFPUTNearResonantGridCertificate
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
open ArchonPhysics.EqualMassPeriodicFPUTUmklappCollisionChartAdapter
open ArchonPhysics.EqualMassPeriodicFPUTUmklappFiniteAtlas
open ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian
open ArchonPhysics.Lattice
open ArchonPhysics.NormalizedResonancePeakKernel
open Filter MeasureTheory Topology

noncomputable section

theorem equalMassPeriodicFPUT_canonicalRootGridAngleError_consumer
    (N : Nat) [NeZero N] {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁) :
    |gridWaveNumber N (canonicalPositiveRootGridMode N k₀ k₁) -
        umklappArcsineRoot
          (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁| <
      2 * Real.pi / (N : Real) :=
  canonicalPositiveRootGridMode_error
    N hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc

theorem equalMassPeriodicFPUT_canonicalRootGridMismatchError_consumer
    (N : Nat) [NeZero N] {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁) :
    |umklappReducedFourWaveMismatch k₀ k₁
        (gridWaveNumber N (canonicalPositiveRootGridMode N k₀ k₁))| <
      4 * Real.pi / (N : Real) :=
  canonicalPositiveRootGridMode_mismatch_abs_lt
    N hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc

theorem equalMassPeriodicFPUT_nearCertificateDiscreteMismatch_consumer
    {N : Nat} [NeZero N] {alpha : Real}
    {out : ActualInteractionBranchMode N}
    {diagram : ActiveFeedbackEffectiveDiagramImage N out}
    (certificate : NearResonantExplicitCollisionKernelCertificate
      alpha out diagram) :
    |reducedTwoToTwoMismatch
        (outputMomentum (reachableEffectiveDiagram diagram))
        (canonicalTwoToTwoExternalModes (reachableEffectiveDiagram diagram) 1)
        (canonicalTwoToTwoExternalModes (reachableEffectiveDiagram diagram) 2)| <
      4 * Real.pi / (N : Real) :=
  certificate.discreteMismatch_abs_lt

theorem equalMassPeriodicFPUT_nearCertificateLocalRatePositive_consumer
    {N : Nat} [NeZero N] {alpha : Real}
    {out : ActualInteractionBranchMode N}
    {diagram : ActiveFeedbackEffectiveDiagramImage N out}
    (certificate : NearResonantExplicitCollisionKernelCertificate
      alpha out diagram) :
    0 < actualRootedLocalCollisionRate alpha out diagram :=
  certificate.rate_pos

theorem equalMassPeriodicFPUT_nearCertificateCollisionLimit_consumer
    {N : Nat} [NeZero N] {alpha : Real}
    {out : ActualInteractionBranchMode N}
    {diagram : ActiveFeedbackEffectiveDiagramImage N out}
    (certificate : NearResonantExplicitCollisionKernelCertificate
      alpha out diagram) :
    Tendsto
      (fun T : Real ↦ ∫ z in
        umklappArcsineLocalLeft
            (umklappPositiveArcsineBranch
              (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
            (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)..
          umklappArcsineLocalRight
            (umklappPositiveArcsineBranch
              (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
            (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram),
        normalizedFiniteTimeResonanceKernel
            (umklappReducedFourWaveMismatch
              (canonicalDiagramGridK₀ diagram)
              (canonicalDiagramGridK₁ diagram) z) T *
          actualRootedLocalCollisionMark alpha out diagram z)
      atTop (nhds (actualRootedLocalCollisionRate alpha out diagram)) :=
  certificate.collision_limit

theorem equalMassPeriodicFPUT_nearGridSincArgumentVanishes_consumer
    (k₀ k₁ time : Nat → Real)
    (hk₀0 : ∀ n, 0 < k₀ n) (hk₀2pi : ∀ n, k₀ n < 2 * Real.pi)
    (hk₁0 : ∀ n, 0 < k₁ n) (hk₁2pi : ∀ n, k₁ n < 2 * Real.pi)
    (hdisc : ∀ n, 0 < umklappTransverseDiscriminant (k₀ n) (k₁ n))
    (hscale : Tendsto
      (fun n : Nat ↦ time n / ((n + 1 : Nat) : Real))
      atTop (nhds 0)) :
    Tendsto
      (fun n : Nat ↦
        umklappReducedFourWaveMismatch (k₀ n) (k₁ n)
            (gridWaveNumber (n + 1)
              (canonicalPositiveRootGridMode (n + 1) (k₀ n) (k₁ n))) *
          time n / 2)
      atTop (nhds 0) :=
  canonicalRootGrid_sincArgument_tendsto_zero
    k₀ k₁ time hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc hscale

theorem equalMassPeriodicFPUT_nearGridSincWeightTendsToOne_consumer
    (k₀ k₁ time : Nat → Real)
    (hk₀0 : ∀ n, 0 < k₀ n) (hk₀2pi : ∀ n, k₀ n < 2 * Real.pi)
    (hk₁0 : ∀ n, 0 < k₁ n) (hk₁2pi : ∀ n, k₁ n < 2 * Real.pi)
    (hdisc : ∀ n, 0 < umklappTransverseDiscriminant (k₀ n) (k₁ n))
    (hscale : Tendsto
      (fun n : Nat ↦ time n / ((n + 1 : Nat) : Real))
      atTop (nhds 0)) :
    Tendsto
      (fun n : Nat ↦
        Real.sinc
          (umklappReducedFourWaveMismatch (k₀ n) (k₁ n)
              (gridWaveNumber (n + 1)
                (canonicalPositiveRootGridMode (n + 1) (k₀ n) (k₁ n))) *
            time n / 2) ^ 2)
      atTop (nhds 1) :=
  canonicalRootGrid_sincSquare_tendsto_one
    k₀ k₁ time hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc hscale

#print axioms equalMassPeriodicFPUT_canonicalRootGridAngleError_consumer
#print axioms equalMassPeriodicFPUT_canonicalRootGridMismatchError_consumer
#print axioms equalMassPeriodicFPUT_nearCertificateDiscreteMismatch_consumer
#print axioms equalMassPeriodicFPUT_nearCertificateLocalRatePositive_consumer
#print axioms equalMassPeriodicFPUT_nearCertificateCollisionLimit_consumer
#print axioms equalMassPeriodicFPUT_nearGridSincArgumentVanishes_consumer
#print axioms equalMassPeriodicFPUT_nearGridSincWeightTendsToOne_consumer

end

end ArchonPhysicsConsumers.Thermalization
